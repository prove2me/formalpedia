-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.lemma_c_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:39:47.761799+00:00
-- url     : https://prove2.me/submissions/b86dc402-7db4-4674-b093-adb5f55276f4

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ,
      distFEA A b σ x ≤ c * max (qNorm 1 (A *ᵥ x - b) - σ) 0 := by
        obtain ⟨l, hl⟩ : ∃ l : Fin m → EuclideanSpace ℝ (Fin n) → ℝ,
            ∀ i v, l i v = ∑ j, A i j * v j := ⟨_, fun _ _ => rfl⟩
        have hl_add : ∀ i u v, l i (u + v) = l i u + l i v := by
          intro i u v; simp [hl, mul_add, Finset.sum_add_distrib]
        have hl_smul : ∀ i (c : ℝ) v, l i (c • v) = c * l i v := by
          intro i c v; simp [hl, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
        have hl_cont : ∀ i, Continuous (l i) := by
          intro i
          have : l i = fun v : EuclideanSpace ℝ (Fin n) => ∑ j, A i j * v j := funext (hl i)
          rw [this]; fun_prop
        obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℝ,
            ∀ v, G v = ∑ i, |l i v - b i| := ⟨_, fun _ => rfl⟩
        have hGcont : Continuous G := by
          have : G = fun v => ∑ i, |l i v - b i| := funext hG
          rw [this]
          exact continuous_finsetSum _ (fun i _ => ((hl_cont i).sub continuous_const).abs)
        have hlink : ∀ y : Fin n → ℝ, qNorm 1 (A *ᵥ y - b) = G (WithLp.toLp 2 y) := by
          intro y
          unfold qNorm
          rw [PiLp.norm_eq_of_L1, hG]
          apply Finset.sum_congr rfl; intro i _
          simp [hl, Matrix.mulVec, dotProduct, Real.norm_eq_abs]
        set K : Set (EuclideanSpace ℝ (Fin n)) := {v | G v ≤ σ} with hK
        have hKconv : Convex ℝ K := by
          intro u hu v hv a c ha hc hac
          simp only [hK, Set.mem_ofPred_eq] at hu hv ⊢
          rw [hG] at hu hv ⊢
          have : ∀ i, |l i (a • u + c • v) - b i| ≤ a * |l i u - b i| + c * |l i v - b i| := by
            intro i
            have e : l i (a • u + c • v) - b i = a * (l i u - b i) + c * (l i v - b i) := by
              rw [hl_add, hl_smul, hl_smul]; linear_combination (b i) * hac
            rw [e]
            calc _ ≤ |a * (l i u - b i)| + |c * (l i v - b i)| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hc]
          calc _ ≤ ∑ i, (a * |l i u - b i| + c * |l i v - b i|) := Finset.sum_le_sum (fun i _ => this i)
            _ = a * ∑ i, |l i u - b i| + c * ∑ i, |l i v - b i| := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            _ ≤ a * σ + c * σ := by gcongr
            _ = σ := by rw [← add_mul, hac, one_mul]
        have hKclosed : IsClosed K := isClosed_le hGcont continuous_const
        have hKne : K.Nonempty := by
          obtain ⟨y, hy⟩ := hfeas
          exact ⟨WithLp.toLp 2 y, by simp only [hK, Set.mem_ofPred_eq]; rw [← hlink]; exact hy⟩
        have hdist : ∀ x : Fin n → ℝ, distFEA A b σ x = Metric.infDist (WithLp.toLp 2 x) K := by
          intro x
          unfold distFEA
          congr 1
          ext v
          constructor
          · rintro ⟨y, hy, rfl⟩
            simp only [hK, Set.mem_ofPred_eq]; rw [← hlink]; exact hy
          · intro hv
            refine ⟨WithLp.ofLp v, ?_, by simp⟩
            show qNorm 1 (A *ᵥ WithLp.ofLp v - b) ≤ σ
            rw [hlink]; simpa using (show G v ≤ σ from hv)
        have lowS : ∀ r a t : ℝ, 0 ≤ t →
            |r| + t * (if SignType.sign r = 0 then |a| else ((SignType.sign r : SignType) : ℝ) * a)
              ≤ |r + t * a| := by
          intro r a t ht
          rcases lt_trichotomy r 0 with h | h | h
          · simp only [sign_neg h, reduceCtorEq, if_false, SignType.coe_neg_one]
            rw [abs_of_neg h]
            have := neg_abs_le (r + t * a)
            linarith [neg_le_abs (r + t * a)]
          · subst h
            simp [abs_mul, abs_of_nonneg ht]
          · simp only [sign_pos h, reduceCtorEq, if_false, SignType.coe_one]
            rw [abs_of_pos h]
            linarith [le_abs_self (r + t * a)]
        have evS : ∀ r a : ℝ, ∀ᶠ t in 𝓝[>] (0:ℝ),
            |r + t * a| = |r| + t * (if SignType.sign r = 0 then |a| else ((SignType.sign r : SignType) : ℝ) * a) := by
          intro r a
          have htend : Filter.Tendsto (fun t : ℝ => r + t * a) (𝓝[>] (0:ℝ)) (𝓝 r) := by
            have : Filter.Tendsto (fun t : ℝ => r + t * a) (𝓝 (0:ℝ)) (𝓝 (r + 0 * a)) :=
              ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
            rw [zero_mul, add_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
          rcases lt_trichotomy r 0 with h | h | h
          · filter_upwards [htend.eventually (gt_mem_nhds h)] with t ht
            simp only [sign_neg h, reduceCtorEq, if_false, SignType.coe_neg_one]
            rw [abs_of_neg h, abs_of_neg ht]; ring
          · subst h
            filter_upwards [self_mem_nhdsWithin] with t ht
            have ht' : (0:ℝ) < t := ht
            simp [abs_mul, abs_of_pos ht']
          · filter_upwards [htend.eventually (lt_mem_nhds h)] with t ht
            simp only [sign_pos h, reduceCtorEq, if_false, SignType.coe_one]
            rw [abs_of_pos h, abs_of_pos ht]; ring
        obtain ⟨φ, hφ⟩ : ∃ φ : (Fin m → SignType) → EuclideanSpace ℝ (Fin n) → ℝ,
            ∀ π d, φ π d = ∑ i, (if π i = 0 then |l i d| else ((π i : SignType) : ℝ) * l i d) :=
          ⟨_, fun _ _ => rfl⟩
        obtain ⟨pat, hpat⟩ : ∃ pat : EuclideanSpace ℝ (Fin n) → (Fin m → SignType),
            ∀ p i, pat p i = SignType.sign (l i p - b i) := ⟨_, fun _ _ => rfl⟩
        have hφcont : ∀ π, Continuous (φ π) := by
          intro π
          have : φ π = fun d => ∑ i, (if π i = 0 then |l i d| else ((π i : SignType) : ℝ) * l i d) :=
            funext (hφ π)
          rw [this]
          refine continuous_finsetSum _ (fun i _ => ?_)
          split_ifs
          · exact (hl_cont i).abs
          · exact continuous_const.mul (hl_cont i)
        have hGpt : ∀ p d (t : ℝ), G (p + t • d) = ∑ i, |(l i p - b i) + t * l i d| := by
          intro p d t
          rw [hG]; apply Finset.sum_congr rfl; intro i _
          rw [hl_add, hl_smul]; ring_nf
        have low : ∀ p d (t : ℝ), 0 ≤ t → G p + t * φ (pat p) d ≤ G (p + t • d) := by
          intro p d t ht
          rw [hGpt, hG, hφ, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum; intro i _
          rw [hpat]; exact lowS _ _ _ ht
        have ev : ∀ p d, ∀ᶠ t in 𝓝[>] (0:ℝ), G (p + t • d) = G p + t * φ (pat p) d := by
          intro p d
          have := Filter.eventually_all.2 (fun i => evS (l i p - b i) (l i d))
          filter_upwards [this] with t ht
          rw [hGpt, hG, hφ, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _
          rw [hpat]; exact ht i
        have claimA : ∀ π, ∃ c > 0, ∀ d p, ‖d‖ = 1 → p ∈ K → pat p = π →
            (∀ w ∈ K, inner ℝ d (w - p) ≤ 0) → c ≤ φ π d := by
          intro π
          set N : Set (EuclideanSpace ℝ (Fin n)) :=
            {d | ‖d‖ = 1 ∧ ∃ p ∈ K, pat p = π ∧ ∀ w ∈ K, inner ℝ d (w - p) ≤ 0} with hNdef
          rcases N.eq_empty_or_nonempty with hN | hN
          · refine ⟨1, one_pos, fun d p hd hp hpp hw => ?_⟩
            exfalso
            have : d ∈ N := ⟨hd, p, hp, hpp, hw⟩
            rw [hN] at this; exact this
          · have hsub : closure N ⊆ Metric.sphere 0 1 :=
              closure_minimal (fun d hd => by simpa using hd.1) Metric.isClosed_sphere
            have hcpt : IsCompact (closure N) :=
              (isCompact_sphere 0 1).of_isClosed_subset isClosed_closure hsub
            obtain ⟨d0, hd0, hmin⟩ :=
              hcpt.exists_isMinOn (hN.mono subset_closure) (hφcont π).continuousOn
            have hd0n : ‖d0‖ = 1 := by simpa using hsub hd0
            have hpos : 0 < φ π d0 := by
              by_contra hneg
              push_neg at hneg
              obtain ⟨d', hd'N, hdd⟩ := Metric.mem_closure_iff.1 hd0 1 one_pos
              obtain ⟨hd'n, p, hp, hpp, hw⟩ := hd'N
              obtain ⟨t, ht, htpos⟩ := ((ev p d0).and self_mem_nhdsWithin).exists
              have htpos' : (0:ℝ) < t := htpos
              have hin : p + t • d0 ∈ K := by
                show G (p + t • d0) ≤ σ
                rw [ht, hpp]
                have : G p ≤ σ := hp
                nlinarith
              have h1 := hw _ hin
              rw [add_sub_cancel_left, real_inner_smul_right] at h1
              have h2 : inner ℝ d' d0 ≤ 0 := by
                by_contra h2; push_neg at h2; nlinarith [mul_pos htpos' h2]
              have h3 := norm_sub_sq_real d0 d'
              rw [← dist_eq_norm, hd0n, hd'n, real_inner_comm] at h3
              have : dist d0 d' ^ 2 < 1 := by nlinarith [dist_nonneg (x := d0) (y := d')]
              nlinarith
            refine ⟨φ π d0, hpos, fun d p hd hp hpp hw => ?_⟩
            exact hmin (subset_closure ⟨hd, p, hp, hpp, hw⟩)
        choose cf hcfpos hcf using claimA
        have hCpos : 0 < ∑ π, (cf π)⁻¹ :=
          Finset.sum_pos (fun π _ => inv_pos.2 (hcfpos π)) Finset.univ_nonempty
        refine ⟨∑ π, (cf π)⁻¹, hCpos, ?_⟩
        intro x
        rw [hdist x, hlink x]
        set v := WithLp.toLp 2 x with hvdef
        by_cases hv : G v ≤ σ
        · rw [Metric.infDist_zero_of_mem (show v ∈ K from hv)]
          exact mul_nonneg hCpos.le (le_max_right _ _)
        · push_neg at hv
          obtain ⟨p, hp, hpeq⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKclosed.isComplete hKconv v
          have hnorm := (norm_eq_iInf_iff_real_inner_le_zero hKconv hp).1 hpeq
          have hvp : v ≠ p := fun h => by
            rw [h] at hv; exact absurd (show G p ≤ σ from hp) (not_le.2 hv)
          set t := ‖v - p‖ with htdef
          have htpos : 0 < t := norm_pos_iff.2 (sub_ne_zero.2 hvp)
          set d := t⁻¹ • (v - p) with hddef
          have hdn : ‖d‖ = 1 := by
            rw [hddef, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ htpos.ne'
          have hdw : ∀ w ∈ K, inner ℝ d (w - p) ≤ 0 := by
            intro w hw
            rw [hddef, real_inner_smul_left]
            exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htpos.le) (hnorm w hw)
          have hvpd : v = p + t • d := by
            rw [hddef, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul, add_sub_cancel]
          have hGp : G p = σ := by
            by_contra hne
            have hlt : G p < σ := lt_of_le_of_ne hp hne
            have htend : Filter.Tendsto (fun s : ℝ => G p + s * φ (pat p) d) (𝓝[>] 0) (𝓝 (G p)) := by
              have : Filter.Tendsto (fun s : ℝ => G p + s * φ (pat p) d) (𝓝 (0:ℝ))
                  (𝓝 (G p + 0 * φ (pat p) d)) :=
                ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
              rw [zero_mul, add_zero] at this
              exact this.mono_left nhdsWithin_le_nhds
            obtain ⟨s, ⟨hs1, hs2⟩, hs3⟩ :=
              (((ev p d).and (htend.eventually (gt_mem_nhds hlt))).and self_mem_nhdsWithin).exists
            have hin : p + s • d ∈ K := show G _ ≤ σ by rw [hs1]; exact hs2.le
            have h1 := hdw _ hin
            rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hdn] at h1
            have : (0:ℝ) < s := hs3
            nlinarith
          have hc := hcf (pat p) d p hdn hp rfl hdw
          have hlow := low p d t htpos.le
          rw [← hvpd, hGp] at hlow
          calc Metric.infDist v K ≤ dist v p := Metric.infDist_le_dist_of_mem hp
            _ = t := dist_eq_norm _ _
            _ ≤ (cf (pat p))⁻¹ * (G v - σ) := by
                rw [le_inv_mul_iff₀ (hcfpos _)]; nlinarith
            _ ≤ (∑ π, (cf π)⁻¹) * max (G v - σ) 0 := by
                rw [max_eq_left (by linarith)]
                apply mul_le_mul_of_nonneg_right _ (by linarith)
                exact Finset.single_le_sum (f := fun π => (cf π)⁻¹)
                  (fun π _ => (inv_pos.2 (hcfpos π)).le) (Finset.mem_univ _)
