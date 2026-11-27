-- Prove2me | solution 1 for SparseLpLq.SmallP.Supplement.theorem_c_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:03.576092+00:00
-- url     : https://prove2.me/submissions/c3a4f64a-4edf-4728-bf4f-15d53667eef3

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting
import Definitions.Def_SparseLpLq_SmallP_Supplement_Penalty

open scoped ENNReal Matrix Topology

open SparseLpLq
open SparseLpLq.SmallP
open SparseLpLq.SmallP.Supplement

open SparseLpLq.SmallP
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (σ : ℝ)
    (hσ : 0 ≤ σ) (hfeas : (FEA A b σ 1).Nonempty) (hb : σ < qNorm 1 b)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → ℝ) (hx : IsLocalMin14 A b σ p x) :
    ∃ lamStar : ℝ, 0 < lamStar ∧ ∀ lam : ℝ, lamStar ≤ lam → IsLocalMinPen A b σ p lam x := by
      obtain ⟨hp0, hp1⟩ := hp
      have hf : ∀ y : Fin n → ℝ, lpObj p y = ∑ j, |y j| ^ p := fun y => by simp [lpObj, hp0.ne']
      have hg : ∀ v : Fin m → ℝ, qNorm 1 v = ∑ i, |v i| := fun v => by
        simp [qNorm, PiLp.norm_eq_of_L1]
      have hmv : ∀ i, Continuous fun e : Fin n → ℝ => (A *ᵥ e) i := fun i => by
        simp only [Matrix.mulVec, dotProduct]; fun_prop
      have hxF' : qNorm 1 (A *ᵥ x - b) ≤ σ := hx.1
      rcases lt_or_eq_of_le hxF' with hlt | heq
      · refine ⟨1, one_pos, fun lam hlam => ?_⟩
        have hcont : Continuous fun y : Fin n → ℝ => qNorm 1 (A *ᵥ y - b) := by
          simp only [hg]
          exact continuous_finsetSum _ fun i _ => ((hmv i).sub continuous_const).abs
        have h1 : ∀ᶠ y in 𝓝 x, qNorm 1 (A *ᵥ y - b) < σ := hcont.continuousAt.eventually (eventually_lt_nhds hlt)
        filter_upwards [h1, hx.2] with y hy1 hy2
        have h3 := hy2 (show y ∈ FEA A b σ 1 from hy1.le)
        unfold Fpen
        have : max (qNorm 1 (A *ᵥ x - b) - σ) 0 = 0 := max_eq_right (by linarith)
        have : 0 ≤ max (qNorm 1 (A *ᵥ y - b) - σ) 0 := le_max_right _ _
        rw [‹max (qNorm 1 (A *ᵥ x - b) - σ) 0 = 0›]
        nlinarith
      -- active case
      have habs : ∀ u s : ℝ, u ≠ 0 → |s| < |u| → |u + s| = |u| + (SignType.sign u : ℝ) * s := by
        intro u s hu hs
        rcases lt_or_gt_of_ne hu with h | h
        · rw [abs_of_neg h] at hs ⊢
          rw [sign_neg h, abs_of_neg (by linarith [le_abs_self s])]
          simp; ring
        · rw [abs_of_pos h] at hs ⊢
          rw [sign_pos h, abs_of_pos (by linarith [neg_abs_le s])]
          simp
      obtain ⟨r, hr⟩ : ∃ r : Fin m → ℝ, r = A *ᵥ x - b := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Fin m → ℝ → ℝ,
          k = fun i a => if r i = 0 then |a| else (SignType.sign (r i) : ℝ) * a := ⟨_, rfl⟩
      have k1 : ∀ i a, |r i| + k i a ≤ |r i + a| := by
        intro i a
        rw [hk]; dsimp only
        split_ifs with h0
        · simp [h0]
        · rcases lt_or_gt_of_ne h0 with h | h
          · rw [sign_neg h, abs_of_neg h]; simp; linarith [neg_le_abs (r i + a)]
          · rw [sign_pos h, abs_of_pos h]; simp; linarith [le_abs_self (r i + a)]
      have k2 : ∀ i a c, k i a - |c| ≤ k i (a + c) := by
        intro i a c
        rw [hk]; dsimp only
        split_ifs with h0
        · have := abs_add_le (a + c) (-c); simp at this; linarith
        · rcases lt_or_gt_of_ne h0 with h | h
          · rw [sign_neg h]; simp; linarith [le_abs_self c]
          · rw [sign_pos h]; simp; linarith [neg_abs_le c]
      have k3 : ∀ i a t, 0 ≤ t → k i (t * a) = t * k i a := by
        intro i a t ht
        rw [hk]; dsimp only
        split_ifs with h0
        · rw [abs_mul, abs_of_nonneg ht]
        · ring
      have k4 : ∀ i a, ∀ᶠ t in 𝓝[>] (0:ℝ), |r i + t * a| = |r i| + t * k i a := by
        intro i a
        by_cases h0 : r i = 0
        · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
          rw [hk]; simp [h0, abs_mul, abs_of_pos ht]
        · have ht : Filter.Tendsto (fun t : ℝ => t * a) (𝓝[>] 0) (𝓝 0) :=
            ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
          filter_upwards [ht.eventually (Metric.ball_mem_nhds 0 (abs_pos.2 h0))] with t htt
          simp only [Real.dist_eq, sub_zero] at htt
          rw [habs _ _ h0 htt, hk]; simp [h0]; ring
      have kc : ∀ i, Continuous (k i) := by
        intro i; rw [hk]; dsimp only
        split_ifs
        · exact continuous_abs
        · exact continuous_const.mul continuous_id
      obtain ⟨w, hw⟩ : ∃ w : Fin n → ℝ, w = fun j => (SignType.sign (x j) : ℝ) * p * |x j| ^ (p - 1) :=
        ⟨_, rfl⟩
      have w1 : ∀ j, x j ≠ 0 → ∀ᶠ s in 𝓝 (0:ℝ),
          |x j + s| ^ p ≤ |x j| ^ p + w j * s ∧ (s ≠ 0 → |x j + s| ^ p < |x j| ^ p + w j * s) := by
        intro j hj
        have hu : 0 < |x j| := abs_pos.2 hj
        filter_upwards [Metric.ball_mem_nhds (0:ℝ) hu] with s hs
        simp only [Real.dist_eq, sub_zero, Metric.mem_ball] at hs
        rw [habs _ _ hj hs]
        set u := |x j| with hu_def
        set δ := (SignType.sign (x j) : ℝ) * s with hδ
        have hsg : |(SignType.sign (x j) : ℝ)| = 1 := by
          rcases lt_or_gt_of_ne hj with h | h
          · rw [sign_neg h]; simp
          · rw [sign_pos h]; simp
        have hδabs : |δ| = |s| := by rw [hδ, abs_mul, hsg, one_mul]
        have hδ1 : -1 ≤ δ / u := by
          rw [le_div_iff₀ hu]; linarith [neg_abs_le δ]
        have hfac : u + δ = u * (1 + δ / u) := by field_simp
        have hwj : w j * s = p * u ^ (p - 1) * δ := by rw [hw, hδ]; ring
        have hrp : u ^ p * (1 + p * (δ / u)) = u ^ p + w j * s := by
          rw [hwj, Real.rpow_sub_one hu.ne']; field_simp
        have hpow : (u + δ) ^ p = u ^ p * (1 + δ / u) ^ p := by
          rw [hfac, Real.mul_rpow hu.le (by linarith)]
        have hup : 0 < u ^ p := Real.rpow_pos_of_pos hu p
        refine ⟨?_, fun hs0 => ?_⟩
        · rw [hpow, ← hrp]
          exact mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self hδ1 hp0.le hp1.le) hup.le
        · rw [hpow, ← hrp]
          have hne : δ / u ≠ 0 := by
            rw [div_ne_zero_iff]; refine ⟨?_, hu.ne'⟩
            intro h0; apply hs0; rw [← abs_eq_zero, ← hδabs, h0, abs_zero]
          exact mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self hδ1 hne hp0 hp1) hup
      have w2 : ∀ ε > 0, ∀ j, x j ≠ 0 → ∀ᶠ z in 𝓝 (x j),
          |x j| ^ p + w j * (z - x j) - ε * |z - x j| ≤ |z| ^ p := by
        intro ε hε j hj
        have hd : HasDerivAt (fun z : ℝ => |z| ^ p) (w j) (x j) := by
          rw [hw]; exact (hasDerivAt_abs hj).rpow_const (Or.inl (abs_ne_zero.2 hj))
        have := (hasDerivAt_iff_isLittleO.1 hd).def hε
        filter_upwards [this] with z hz
        simp only [Real.norm_eq_abs, smul_eq_mul] at hz
        have := neg_abs_le (|z| ^ p - |x j| ^ p - (z - x j) * w j)
        nlinarith
      have w3 : ∀ K : ℝ, ∀ᶠ z in 𝓝 (0:ℝ), K * |z| ≤ |z| ^ p := by
        intro K
        have hq : 0 < 1 - p := by linarith
        have hc : Continuous fun z : ℝ => |z| ^ (1 - p) :=
          continuous_abs.rpow_const (fun _ => Or.inr hq.le)
        have h0 : (fun z : ℝ => |z| ^ (1 - p)) 0 = 0 := by simp [Real.zero_rpow hq.ne']
        have hK : (0:ℝ) < 1 / (|K| + 1) := by positivity
        have := hc.continuousAt (x := 0) |>.eventually (eventually_lt_nhds (h0 ▸ hK))
        filter_upwards [this] with z hz
        by_cases hz0 : z = 0
        · simp [hz0, Real.zero_rpow hp0.ne']
        have hzp : 0 < |z| := abs_pos.2 hz0
        have hsplit : |z| = |z| ^ p * |z| ^ (1 - p) := by
          rw [← Real.rpow_add hzp]; simp
        have h1 : 0 ≤ |z| ^ p := (Real.rpow_pos_of_pos hzp p).le
        have h2 : 0 ≤ |z| ^ (1 - p) := (Real.rpow_pos_of_pos hzp _).le
        have h3 : (|K| + 1) * |z| ^ (1 - p) ≤ 1 := by
          have := hz; rw [lt_div_iff₀ (by positivity)] at this; linarith
        have h4 : K * |z| ≤ (|K| + 1) * |z| := by
          have := le_abs_self K; nlinarith
        calc K * |z| ≤ (|K| + 1) * |z| := h4
          _ = (|K| + 1) * (|z| ^ p * |z| ^ (1 - p)) := by rw [← hsplit]
          _ = |z| ^ p * ((|K| + 1) * |z| ^ (1 - p)) := by ring
          _ ≤ |z| ^ p * 1 := mul_le_mul_of_nonneg_left h3 h1
          _ = |z| ^ p := mul_one _
      obtain ⟨h, hh⟩ : ∃ h : (Fin n → ℝ) → ℝ, h = fun e => ∑ i, k i ((A *ᵥ e) i) := ⟨_, rfl⟩
      obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin n → ℝ) → ℝ, Φ = fun e => ∑ j, w j * e j := ⟨_, rfl⟩
      obtain ⟨N1, hN1⟩ : ∃ N1 : (Fin n → ℝ) → ℝ, N1 = fun e => ∑ j, |e j| := ⟨_, rfl⟩
      have hgsum : ∀ y, qNorm 1 (A *ᵥ y - b) = ∑ i, |r i + (A *ᵥ (y - x)) i| := by
        intro y; rw [hg, hr]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Matrix.mulVec_sub]
      have hrσ : ∑ i, |r i| = σ := by rw [← hg, hr, heq]
      have key : ∀ e : Fin n → ℝ, (∀ j, x j = 0 → e j = 0) → N1 e = 1 → 0 < max (Φ e) (h e) := by
        intro e heV hN
        by_contra hle
        push Not at hle
        have hΦe : Φ e ≤ 0 := le_trans (le_max_left _ _) hle
        have hhe : h e ≤ 0 := le_trans (le_max_right _ _) hle
        have ht : Filter.Tendsto (fun t : ℝ => x + t • e) (𝓝[>] 0) (𝓝 x) :=
          ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 x
            (by simp)).mono_left nhdsWithin_le_nhds
        have E1 := ht.eventually hx.2
        have E2 : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, |r i + t * (A *ᵥ e) i| = |r i| + t * k i ((A *ᵥ e) i) :=
          Filter.eventually_all.2 fun i => k4 i _
        have E3 : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ j, x j ≠ 0 →
            (|x j + t * e j| ^ p ≤ |x j| ^ p + w j * (t * e j) ∧
              (t * e j ≠ 0 → |x j + t * e j| ^ p < |x j| ^ p + w j * (t * e j))) := by
          refine Filter.eventually_all.2 fun j => ?_
          by_cases hj : x j = 0
          · exact Filter.Eventually.of_forall fun t h' => absurd hj h'
          · have htj : Filter.Tendsto (fun t : ℝ => t * e j) (𝓝[>] 0) (𝓝 0) :=
              ((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
            filter_upwards [htj.eventually (w1 j hj)] with t ht' _ using ht'
        have E4 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
        obtain ⟨t, h1, h2, h3, h4⟩ := (E1.and (E2.and (E3.and E4))).exists
        have hfe : x + t • e ∈ FEA A b σ 1 := by
          show qNorm 1 (A *ᵥ (x + t • e) - b) ≤ σ
          rw [hgsum]
          simp only [add_sub_cancel_left, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
          rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib, hrσ, ← Finset.mul_sum]
          have : ∑ i, k i ((A *ᵥ e) i) = h e := by rw [hh]
          rw [this]; nlinarith
        have hle2 := h1 hfe
        rw [hf, hf] at hle2
        obtain ⟨j0, hj0⟩ : ∃ j0, e j0 ≠ 0 := by
          by_contra hc; push Not at hc
          rw [hN1] at hN; simp [hc] at hN
        have hx0 : x j0 ≠ 0 := fun h0 => hj0 (heV j0 h0)
        have hlt : ∑ j, |(x + t • e) j| ^ p < ∑ j, (|x j| ^ p + w j * (t * e j)) := by
          apply Finset.sum_lt_sum
          · intro j _
            by_cases hj : x j = 0
            · simp [hj, heV j hj]
            · simpa using (h3 j hj).1
          · exact ⟨j0, Finset.mem_univ _, by simpa using (h3 j0 hx0).2 (mul_ne_zero h4.ne' hj0)⟩
        rw [Finset.sum_add_distrib] at hlt
        have : ∑ j, w j * (t * e j) = t * Φ e := by
          rw [hΦ, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [this] at hlt
        nlinarith
      have hhc : Continuous h := by
        rw [hh]; exact continuous_finsetSum _ fun i _ => (kc i).comp (hmv i)
      have hΦc : Continuous Φ := by
        rw [hΦ]; exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
      have hN1c : Continuous N1 := by
        rw [hN1]; exact continuous_finsetSum _ fun j _ => (continuous_apply j).abs
      have hhom : ∀ t : ℝ, 0 ≤ t → ∀ e, max (Φ (t • e)) (h (t • e)) = t * max (Φ e) (h e) := by
        intro t ht e
        have e1 : Φ (t • e) = t * Φ e := by
          rw [hΦ]; simp only [Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        have e2 : h (t • e) = t * h e := by
          rw [hh]; simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => k3 i _ t ht
        rw [e1, e2, mul_max_of_nonneg _ _ ht]
      have hN1hom : ∀ t : ℝ, 0 ≤ t → ∀ e, N1 (t • e) = t * N1 e := by
        intro t ht e
        rw [hN1]; simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht]; rw [Finset.mul_sum]
      have hN1nn : ∀ e, 0 ≤ N1 e := fun e => by rw [hN1]; positivity
      have hzero : ∀ e, N1 e = 0 → e = 0 := by
        intro e he; rw [hN1] at he
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (e j))).1 he
        funext j; simpa using this j (Finset.mem_univ _)
      have hψ0 : max (Φ 0) (h 0) = 0 := by
        have := hhom 0 le_rfl 0; simpa using this
      set T : Set (Fin n → ℝ) := {e | (∀ j, x j = 0 → e j = 0) ∧ N1 e = 1} with hT
      have hTc : IsCompact T := by
        apply Metric.isCompact_of_isClosed_isBounded
        · show IsClosed ({e : Fin n → ℝ | ∀ j, x j = 0 → e j = 0} ∩ {e | N1 e = 1})
          apply IsClosed.inter
          · have hset : {e : Fin n → ℝ | ∀ j, x j = 0 → e j = 0} =
                ⋂ j, ⋂ (_ : x j = 0), {e : Fin n → ℝ | e j = 0} := by ext; simp
            rw [hset]
            exact isClosed_iInter fun j => isClosed_iInter fun _ =>
              isClosed_eq (continuous_apply j) continuous_const
          · exact isClosed_eq hN1c continuous_const
        · rw [Metric.isBounded_iff_subset_closedBall 0]
          refine ⟨1, fun e he => ?_⟩
          rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
          intro j
          rw [Real.norm_eq_abs, ← he.2, hN1]
          exact Finset.single_le_sum (f := fun j => |e j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      obtain ⟨c, hc0, hcT⟩ : ∃ c > 0, ∀ e ∈ T, c ≤ max (Φ e) (h e) := by
        by_cases hTn : T.Nonempty
        · obtain ⟨e0, he0, hmin⟩ := hTc.exists_isMinOn hTn ((hΦc.max hhc).continuousOn)
          exact ⟨_, key e0 he0.1 he0.2, fun e he => hmin he⟩
        · refine ⟨1, one_pos, fun e he => absurd ⟨e, he⟩ hTn⟩
      have hcV : ∀ e, (∀ j, x j = 0 → e j = 0) → c * N1 e ≤ max (Φ e) (h e) := by
        intro e heV
        rcases (hN1nn e).lt_or_eq with hpos | h0
        · have hmem : (N1 e)⁻¹ • e ∈ T := by
            refine ⟨fun j hj => by simp [heV j hj], ?_⟩
            rw [hN1hom _ (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']
          have h1 := hcT _ hmem
          have h2 := hhom (N1 e) hpos.le ((N1 e)⁻¹ • e)
          rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at h2
          rw [h2]; nlinarith
        · rw [← h0, hzero e h0.symm, hψ0]; simp
      obtain ⟨G, hG⟩ : ∃ G : ℝ, G = ∑ j, |w j| := ⟨_, rfl⟩
      obtain ⟨M, hM⟩ : ∃ M : Fin n → ℝ, M = fun j => ∑ i, |A i j| := ⟨_, rfl⟩
      have hG0 : 0 ≤ G := by rw [hG]; positivity
      refine ⟨(G + c) / c, by positivity, fun lam hlam => ?_⟩
      have hlc : G + c ≤ lam * c := (div_le_iff₀ hc0).1 hlam
      have hlam0 : 0 ≤ lam := le_trans (by positivity) hlam
      have E : ∀ j, ∀ᶠ y in 𝓝 x,
          w j * (if x j = 0 then 0 else y j - x j) - c * |if x j = 0 then 0 else y j - x j|
            + lam * (M j * |if x j = 0 then y j - x j else 0|) ≤ |y j| ^ p - |x j| ^ p := by
        intro j
        have htj := (continuous_apply j).tendsto x
        by_cases hj : x j = 0
        · rw [hj] at htj
          filter_upwards [htj.eventually (w3 (lam * M j))] with y hy
          simp only [hj, if_true, sub_zero, abs_zero, mul_zero, sub_self, Real.zero_rpow hp0.ne']
          linarith
        · filter_upwards [htj.eventually (w2 c hc0 j hj)] with y hy
          simp only [hj, if_false, abs_zero, mul_zero, add_zero]
          linarith
      filter_upwards [Filter.eventually_all.2 E] with y hy
      obtain ⟨dS, hdS⟩ : ∃ dS : Fin n → ℝ, dS = fun j => if x j = 0 then 0 else y j - x j := ⟨_, rfl⟩
      obtain ⟨dN, hdN⟩ : ∃ dN : Fin n → ℝ, dN = fun j => if x j = 0 then y j - x j else 0 := ⟨_, rfl⟩
      have hy' : ∀ j, w j * dS j - c * |dS j| + lam * (M j * |dN j|) ≤ |y j| ^ p - |x j| ^ p := by
        intro j; rw [hdS, hdN]; exact hy j
      have hdec : y - x = dS + dN := by
        funext j; rw [hdS, hdN]; simp only [Pi.sub_apply, Pi.add_apply]; split_ifs <;> simp
      have hsum : Φ dS - c * N1 dS + lam * ∑ j, M j * |dN j| ≤ ∑ j, |y j| ^ p - ∑ j, |x j| ^ p := by
        have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hy' j)
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum] at this
        rw [hΦ, hN1]; exact this
      have hAN : ∑ i, |(A *ᵥ dN) i| ≤ ∑ j, M j * |dN j| := by
        calc ∑ i, |(A *ᵥ dN) i| ≤ ∑ i, ∑ j, |A i j| * |dN j| := by
              refine Finset.sum_le_sum fun i _ => ?_
              simp only [Matrix.mulVec, dotProduct]
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              simp [abs_mul]
          _ = ∑ j, M j * |dN j| := by
              rw [Finset.sum_comm]; rw [hM]; simp only [Finset.sum_mul]
      have hgy : h dS - ∑ j, M j * |dN j| ≤ qNorm 1 (A *ᵥ y - b) - σ := by
        rw [hgsum, hdec, Matrix.mulVec_add]
        have : ∀ i, |r i| + k i ((A *ᵥ dS) i) - |(A *ᵥ dN) i| ≤ |r i| + k i ((A *ᵥ dS) i + (A *ᵥ dN) i) := by
          intro i; linarith [k2 i ((A *ᵥ dS) i) ((A *ᵥ dN) i)]
        have h2 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
          (this i).trans (k1 i ((A *ᵥ dS) i + (A *ᵥ dN) i)))
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrσ] at h2
        simp only [Pi.add_apply]
        have : h dS = ∑ i, k i ((A *ᵥ dS) i) := by rw [hh]
        rw [this]; linarith
      have hcd : c * N1 dS ≤ max (Φ dS) (h dS) := hcV dS (fun j hj => by simp [hdS, hj])
      have hΦlow : -(G * N1 dS) ≤ Φ dS := by
        rw [hΦ, hN1]; simp only
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : |w j| ≤ G := by
          rw [hG]; exact Finset.single_le_sum (f := fun j => |w j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
        have h2 := neg_abs_le (w j * dS j)
        rw [abs_mul] at h2
        nlinarith [abs_nonneg (dS j)]
      have hMnn : 0 ≤ ∑ j, M j * |dN j| := by rw [hM]; positivity
      unfold Fpen
      rw [hf, hf, heq, sub_self, max_self, mul_zero, add_zero]
      have hm0 : 0 ≤ max (qNorm 1 (A *ᵥ y - b) - σ) 0 := le_max_right _ _
      have hm1 : qNorm 1 (A *ᵥ y - b) - σ ≤ max (qNorm 1 (A *ᵥ y - b) - σ) 0 := le_max_left _ _
      rcases le_max_iff.1 hcd with h1 | h1
      · nlinarith [mul_nonneg hlam0 hm0, mul_nonneg hlam0 hMnn]
      · have hA := mul_le_mul_of_nonneg_left hm1 hlam0
        have hB := mul_le_mul_of_nonneg_left hgy hlam0
        have hC := mul_le_mul_of_nonneg_left h1 hlam0
        have hD := mul_nonneg (sub_nonneg.2 hlc) (hN1nn dS)
        nlinarith
