-- Prove2me | solution 1 for SocialManip.Beliefs.Supplement.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:33:13.53786+00:00
-- url     : https://prove2.me/submissions/b58969ed-3229-4169-b3b1-c0d2717ee36e

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

open MeasureTheory ProbabilityTheory Filter Topology

open SocialManip
open SocialManip.Beliefs
open SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem solution {n : ℕ} (M : Model n) (hS : M.Standing) (hG : M.GameDomain)
    (adj : Fin n → Fin n → Prop) (hA : M.Assumption1 adj) (y : State) :
    ∀ᵐ ω ∂(sampleMeasure M y),
      Tendsto (fun T : ℝ => beliefR M y y (fun _ => false) ω T) atTop
        (𝓝 fun _ => truth y State.R) := by
          have slln : ∀ {ι : Type} {X : Type} [MeasurableSpace X] (P : ι → Measure X)
              [∀ k, IsProbabilityMeasure (P k)] (idx : ℕ → ι), Function.Injective idx →
              (∀ l, P (idx l) = P (idx 0)) → ∀ (f : X → ℝ), Measurable f → (∀ x, |f x| ≤ 1) →
              ∀ᵐ ω ∂(Measure.infinitePi P), Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, f (ω (idx l))) / N)
                atTop (𝓝 (∫ x, f x ∂(P (idx 0)))) := by
            intro ι X _ P _ idx hinj hP f hf hb
            have hind := iIndepFun_infinitePi (P := P) (X := fun _ => f) (fun _ => hf)
            have hmp : ∀ l, MeasurePreserving (fun ω : (∀ _ : ι, X) => f (ω (idx l)))
                (Measure.infinitePi P) ((P (idx 0)).map f) := by
              intro l
              have h1 := measurePreserving_eval_infinitePi P (idx l)
              refine ⟨hf.comp h1.measurable, ?_⟩
              have : (fun ω : (∀ _ : ι, X) => f (ω (idx l))) = f ∘ Function.eval (idx l) := rfl
              rw [this, ← Measure.map_map hf h1.measurable, h1.map_eq, hP l]
            have key := strong_law_ae_real (μ := Measure.infinitePi P)
              (fun l ω => f (ω (idx l))) ?_ ?_ ?_
            · have hint : (Measure.infinitePi P)[fun ω => f (ω (idx 0))] = ∫ x, f x ∂(P (idx 0)) := by
                have h1 := measurePreserving_eval_infinitePi P (idx 0)
                rw [← h1.map_eq, integral_map h1.measurable.aemeasurable hf.aestronglyMeasurable]

              rw [hint] at key
              exact key
            · refine Integrable.of_bound (hmp 0).measurable.aestronglyMeasurable 1 ?_
              exact Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hb _
            · intro a b hab
              exact hind.indepFun (hinj.ne hab)
            · intro l
              exact ⟨(hmp l).measurable.aemeasurable, (hmp 0).measurable.aemeasurable,
                by rw [(hmp l).map_eq, (hmp 0).map_eq]⟩
          have hsum2 : ∀ f : State → ℝ, ∑ s, f s = f State.S + f State.R := by
            intro f
            show ∑ s ∈ {State.S, State.R}, f s = _
            rw [Finset.sum_pair (by decide)]
          have hexp0 : ∀ᵐ x ∂(expMeasure 1), 0 ≤ x := by
            rw [ae_iff]
            have h1 : (expMeasure 1).real (Set.Iic 0) = 0 := by
              rw [← cdf_eq_real, cdf_expMeasure_eq one_pos]
              simp
            have h2 : (expMeasure 1) (Set.Iic 0) = 0 := by
              rwa [measureReal_eq_zero_iff] at h1
            refine measure_mono_null (fun x hx => ?_) h2
            simp only [Set.mem_ofPred_eq, not_le] at hx
            exact Set.mem_Iic.2 hx.le
          have hexpmean : 0 < ∫ x, (if 1 < x then (1:ℝ) else 0) ∂(expMeasure 1) := by
            have : (fun x : ℝ => if 1 < x then (1:ℝ) else 0) = (Set.Ioi (1:ℝ)).indicator 1 := by
              funext x; simp [Set.indicator, Set.mem_Ioi]
            rw [this, integral_indicator_one measurableSet_Ioi, ← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, cdf_expMeasure_eq one_pos]
            simp [Real.exp_pos]
          have hber : ∀ i, (∫ s, (if s = y then (1:ℝ) else -1) ∂(bernoulliMeasure State.S State.R
              (clampProb (organicProbS (M.p i) y)))) = 2 * M.p i - 1 := by
            intro i
            have hp := hS.1 i
            have hc : ((clampProb (organicProbS (M.p i) y)) : ℝ) = organicProbS (M.p i) y := by
              unfold clampProb
              rw [Set.coe_projIcc]
              unfold organicProbS
              split_ifs
              · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
              · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
            rw [integral_fintype (Integrable.of_finite), hsum2]
            rw [bernoulliMeasure_real_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp),
              bernoulliMeasure_real_apply_of_notMem_of_mem _ (measurableSet_singleton _) (by simp) (by simp), hc]
            cases y <;> simp [organicProbS] <;> ring
          have hq0 := hG.1
          have hq1 := hG.2.1
          have hlam := hG.2.2.1
          have hBUS1 : ∀ p : ℝ, 1/2 < p → p < 1 → ∀ a d : ℕ,
              0 ≤ BUS p M.q a (a + d) ∧ BUS p M.q a (a + d) ≤ (M.q / (1 - M.q)) * ((1 - p) / p) ^ d := by
            intro p hp1 hp2 a d
            have hp0 : 0 < p := by linarith
            have h1p : 0 < 1 - p := by linarith
            have hu : 0 < p ^ a * (1 - p) ^ (a + d) * M.q := by positivity
            have hv : 0 < p ^ (a + d) * (1 - p) ^ a * (1 - M.q) := by
              have : 0 < 1 - M.q := by linarith
              positivity
            unfold BUS
            refine ⟨by positivity, ?_⟩
            calc p ^ a * (1 - p) ^ (a + d) * M.q / (p ^ a * (1 - p) ^ (a + d) * M.q + p ^ (a + d) * (1 - p) ^ a * (1 - M.q))
                ≤ p ^ a * (1 - p) ^ (a + d) * M.q / (p ^ (a + d) * (1 - p) ^ a * (1 - M.q)) := by
                  apply div_le_div_of_nonneg_left hu.le hv; linarith
              _ = (M.q / (1 - M.q)) * ((1 - p) / p) ^ d := by
                  have : 0 < 1 - M.q := by linarith
                  rw [div_pow, pow_add, pow_add]
                  field_simp
          have hBUS2 : ∀ p : ℝ, 1/2 < p → p < 1 → ∀ a d : ℕ,
              0 ≤ 1 - BUS p M.q (a + d) a ∧ 1 - BUS p M.q (a + d) a ≤ ((1 - M.q) / M.q) * ((1 - p) / p) ^ d := by
            intro p hp1 hp2 a d
            have hp0 : 0 < p := by linarith
            have h1p : 0 < 1 - p := by linarith
            have hq' : 0 < 1 - M.q := by linarith
            have hu : 0 < p ^ (a + d) * (1 - p) ^ a * M.q := by positivity
            have hv : 0 < p ^ a * (1 - p) ^ (a + d) * (1 - M.q) := by positivity
            have heq : 1 - BUS p M.q (a + d) a = p ^ a * (1 - p) ^ (a + d) * (1 - M.q) /
                (p ^ (a + d) * (1 - p) ^ a * M.q + p ^ a * (1 - p) ^ (a + d) * (1 - M.q)) := by
              unfold BUS
              field_simp
              ring
            rw [heq]
            refine ⟨by positivity, ?_⟩
            calc p ^ a * (1 - p) ^ (a + d) * (1 - M.q) /
                (p ^ (a + d) * (1 - p) ^ a * M.q + p ^ a * (1 - p) ^ (a + d) * (1 - M.q))
                ≤ p ^ a * (1 - p) ^ (a + d) * (1 - M.q) / (p ^ (a + d) * (1 - p) ^ a * M.q) := by
                  apply div_le_div_of_nonneg_left hv.le hu; linarith
              _ = ((1 - M.q) / M.q) * ((1 - p) / p) ^ d := by
                  rw [div_pow, pow_add, pow_add]
                  field_simp
          have hPers : ∀ ω : Sample n, (∀ l, 0 ≤ ω.2.1 l) →
              Tendsto (fun N => ∑ l ∈ Finset.range N, ω.2.1 l) atTop atTop → ∀ i, 1/2 < M.p i →
              Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if ω.1 (i, l) = y then (1:ℝ) else -1)) / N)
                atTop (𝓝 (2 * M.p i - 1)) →
              Tendsto (fun T : ℝ => personalR M y (fun _ => false) ω i T) atTop (𝓝 (truth y State.R)) := by
            classical
            intro ω hA hB i hpi hC
            have hp2 := (hS.1 i).2
            set e := ω.2.1 with he
            have hmono : Monotone (fun k => arrivalTime e M.lam k) := by
              apply monotone_nat_of_le_succ
              intro k
              unfold arrivalTime
              apply div_le_div_of_nonneg_right _ hlam.le
              rw [Finset.sum_range_succ _ (k + 1)]
              linarith [hA (k + 1)]
            have hex : ∀ T : ℝ, ∃ k, T < arrivalTime e M.lam k := by
              intro T
              obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_atTop.1 hB) (T * M.lam + 1))
              refine ⟨N, ?_⟩
              unfold arrivalTime
              rw [lt_div_iff₀ hlam]
              have := hN (N + 1) (by omega)
              linarith
            let Nf : ℝ → ℕ := fun T => Nat.find (hex T)
            have hN : ∀ T k, arrivalTime e M.lam k ≤ T ↔ k < Nf T := by
              intro T k
              constructor
              · intro hk
                by_contra hc
                push Not at hc
                have h1 := Nat.find_spec (hex T)
                have h2 := hmono hc
                simp only at h2
                linarith
              · intro hk
                have := Nat.find_min (hex T) hk
                linarith
            have hNt : Tendsto Nf atTop atTop := by
              rw [tendsto_atTop]
              intro K
              rw [eventually_atTop]
              refine ⟨arrivalTime e M.lam K, fun T hT => ?_⟩
              exact ((hN T K).1 hT).le
            let cnt : State → ℕ → ℕ := fun s N => ((Finset.range N).filter (fun k => ω.1 (i, k) = s)).card
            have hcount : ∀ T s, countAt M y (fun _ => false) ω i T s = cnt s (Nf T) := by
              intro T s
              unfold countAt
              simp only [Bool.false_eq_true, false_and, if_false, add_zero]
              show _ = ((Finset.range (Nf T)).filter (fun k => ω.1 (i, k) = s)).card
              rw [← Set.ncard_coe_finset]
              congr 1
              ext k
              simp [← hN T k, he]
            have hpers : ∀ T, personalR M y (fun _ => false) ω i T =
                1 - BUS (M.p i) M.q (cnt State.S (Nf T)) (cnt State.R (Nf T)) := by
              intro T
              unfold personalR
              rw [hcount, hcount]
            -- D → ∞
            have hD : Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if ω.1 (i, l) = y then (1:ℝ) else -1)))
                atTop atTop := by
              have h1 : Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if ω.1 (i, l) = y then (1:ℝ) else -1)) / N
                  * (N : ℝ)) atTop atTop :=
                Tendsto.pos_mul_atTop (by linarith) hC tendsto_natCast_atTop_atTop
              refine h1.congr' ?_
              rw [EventuallyEq, eventually_atTop]
              refine ⟨1, fun N hN => ?_⟩
              have : (N : ℝ) ≠ 0 := by positivity
              field_simp
            have hDeq : ∀ N, (∑ l ∈ Finset.range N, (if ω.1 (i, l) = y then (1:ℝ) else -1)) =
                if y = State.R then (cnt State.R N : ℝ) - cnt State.S N else (cnt State.S N : ℝ) - cnt State.R N := by
              intro N
              rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
              simp only [nsmul_eq_mul, mul_one, mul_neg]
              cases y
              · have : (Finset.range N).filter (fun l => ¬ ω.1 (i, l) = State.S) =
                    (Finset.range N).filter (fun l => ω.1 (i, l) = State.R) := by
                  apply Finset.filter_congr
                  intro l _
                  cases ω.1 (i, l) <;> simp
                rw [this]; simp [cnt]; ring
              · have : (Finset.range N).filter (fun l => ¬ ω.1 (i, l) = State.R) =
                    (Finset.range N).filter (fun l => ω.1 (i, l) = State.S) := by
                  apply Finset.filter_congr
                  intro l _
                  cases ω.1 (i, l) <;> simp
                rw [this]; simp [cnt]; ring
            have hcomp : (fun T => personalR M y (fun _ => false) ω i T) =
                (fun N => 1 - BUS (M.p i) M.q (cnt State.S N) (cnt State.R N)) ∘ Nf := funext hpers
            rw [hcomp]
            refine Tendsto.comp ?_ hNt
            have hρ0 : 0 ≤ (1 - M.p i) / M.p i := div_nonneg (by linarith) (by linarith)
            have hρ1 : (1 - M.p i) / M.p i < 1 := by rw [div_lt_one (by linarith)]; linarith
            -- generic: from a difference tending to infinity, get nat difference
            have hdiff : ∀ a b : ℕ → ℕ, Tendsto (fun N => (b N : ℝ) - a N) atTop atTop →
                (∀ᶠ N in atTop, b N = a N + (b N - a N)) ∧ Tendsto (fun N => b N - a N) atTop atTop := by
              intro a b h
              have hev : ∀ᶠ N in atTop, a N ≤ b N := by
                filter_upwards [h.eventually_ge_atTop 0] with N hN
                have : (a N : ℝ) ≤ b N := by linarith
                exact_mod_cast this
              refine ⟨hev.mono fun N hN => by omega, ?_⟩
              rw [← tendsto_natCast_atTop_iff (R := ℝ)]
              refine h.congr' ?_
              filter_upwards [hev] with N hN
              push_cast [hN]
              ring
            cases y
            · simp only [if_neg (by decide : State.S ≠ State.R)] at hDeq
              have h1 : Tendsto (fun N => (cnt State.S N : ℝ) - cnt State.R N) atTop atTop :=
                hD.congr (fun N => hDeq N)
              obtain ⟨hev, hd⟩ := hdiff (cnt State.R) (cnt State.S) h1
              have hT : truth State.S State.R = 0 := by simp [truth]
              rw [hT]
              have hlim : Tendsto (fun N => ((1 - M.q) / M.q) * ((1 - M.p i) / M.p i) ^ (cnt State.S N - cnt State.R N))
                  atTop (𝓝 0) := by
                have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp hd
                simpa using this.const_mul ((1 - M.q) / M.q)
              refine squeeze_zero' ?_ ?_ hlim
              · filter_upwards [hev] with N hN
                have := hBUS2 (M.p i) hpi hp2 (cnt State.R N) (cnt State.S N - cnt State.R N)
                rw [← hN] at this
                exact this.1
              · filter_upwards [hev] with N hN
                have := hBUS2 (M.p i) hpi hp2 (cnt State.R N) (cnt State.S N - cnt State.R N)
                rw [← hN] at this
                exact this.2
            · simp only [if_true] at hDeq
              have h1 : Tendsto (fun N => (cnt State.R N : ℝ) - cnt State.S N) atTop atTop :=
                hD.congr (fun N => hDeq N)
              obtain ⟨hev, hd⟩ := hdiff (cnt State.S) (cnt State.R) h1
              have hT : truth State.R State.R = 1 - 0 := by simp [truth]
              rw [hT]
              refine tendsto_const_nhds.sub ?_
              have hlim : Tendsto (fun N => (M.q / (1 - M.q)) * ((1 - M.p i) / M.p i) ^ (cnt State.R N - cnt State.S N))
                  atTop (𝓝 0) := by
                have := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp hd
                simpa using this.const_mul (M.q / (1 - M.q))
              refine squeeze_zero' ?_ ?_ hlim
              · filter_upwards [hev] with N hN
                have := hBUS1 (M.p i) hpi hp2 (cnt State.S N) (cnt State.R N - cnt State.S N)
                rw [← hN] at this
                exact this.1
              · filter_upwards [hev] with N hN
                have := hBUS1 (M.p i) hpi hp2 (cnt State.S N) (cnt State.R N - cnt State.S N)
                rw [← hN] at this
                exact this.2
          have hdet : ∀ ω : Sample n, (∀ i, 1/2 < M.p i → Tendsto (fun T : ℝ => personalR M y (fun _ => false) ω i T)
              atTop (𝓝 (truth y State.R))) →
              Tendsto (fun T : ℝ => beliefR M y y (fun _ => false) ω T) atTop (𝓝 fun _ => truth y State.R) := by
            intro ω hP
            set t := truth y State.R with ht
            set g := gridBeliefR M y y (fun _ => false) ω with hg
            set e : ℕ → Fin n → ℝ := fun k j => g k j - t with he
            set δ : ℕ → Fin n → ℝ := fun l j => M.θ j * (personalR M y (fun _ => false) ω j (l : ℕ) - t) with hδdef
            have hαnn : ∀ j ∉ M.B, ∀ l, 0 ≤ M.α j l := hS.2.2.1
            have hθnn : ∀ j ∉ M.B, 0 ≤ M.θ j := hS.2.1
            have hsum1 : ∀ j ∉ M.B, M.θ j + ∑ l, M.α j l = 1 := hS.2.2.2
            have hsα : ∀ j ∉ M.B, ∑ l, M.α j l ≤ 1 := fun j hj => by linarith [hsum1 j hj, hθnn j hj]
            have heB : ∀ k, ∀ j ∈ M.B, e k j = 0 := by
              intro k j hj
              cases k <;> simp [e, g, gridBeliefR, hj, t]
            have hrec : ∀ k, ∀ j ∉ M.B, e (k+1) j = δ (k+1) j + ∑ l, M.α j l * e k l := by
              intro k j hj
              have h1 := hsum1 j hj
              simp only [e, δ, g, gridBeliefR, if_neg hj, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
              linear_combination t * h1
            have hbound : ∀ k, ∀ j ∉ M.B, |e (k+1) j| ≤ |δ (k+1) j| + ∑ l, M.α j l * |e k l| := by
              intro k j hj
              rw [hrec k j hj]
              refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
              refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [abs_mul, abs_of_nonneg (hαnn j hj l)]
            let H : ℕ → ℝ → ℝ → Prop := fun k E η =>
              (∀ j, |e k j| ≤ E) ∧ (∀ l, k < l → ∀ j ∉ M.B, |δ l j| ≤ η)
            have hsumle : ∀ j ∉ M.B, ∀ k (c : ℝ), 0 ≤ c → (∀ l, |e k l| ≤ c) → ∑ l, M.α j l * |e k l| ≤ c := by
              intro j hj k c hc hl
              calc ∑ l, M.α j l * |e k l| ≤ ∑ l, M.α j l * c :=
                    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hl l) (hαnn j hj l)
                _ = (∑ l, M.α j l) * c := by rw [Finset.sum_mul]
                _ ≤ c := mul_le_of_le_one_left hc (hsα j hj)
            have hGen : ∀ k E η, 0 ≤ E → 0 ≤ η → H k E η → ∀ m : ℕ, ∀ j, |e (k+m) j| ≤ m * η + E := by
              intro k E η hE hη hH m
              induction m with
              | zero => intro j; simpa using hH.1 j
              | succ m ih =>
                intro j
                by_cases hj : j ∈ M.B
                · rw [heB _ _ hj]; simp; positivity
                · have h1 := hbound (k+m) j hj
                  have h2 := hH.2 (k + m + 1) (by omega) j hj
                  have h3 := hsumle j hj (k+m) (m * η + E) (by positivity) ih
                  show |e (k + m + 1) j| ≤ _
                  push_cast
                  linarith
            let Q : Fin n → Prop := fun i => ∃ m₀ : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧
              ∀ k E η, 0 ≤ E → 0 ≤ η → H k E η → ∀ m : ℕ, m₀ ≤ m → |e (k+m) i| ≤ m * η + ρ * E
            have QB : ∀ i ∈ M.B, Q i := by
              intro i hi
              refine ⟨0, 0, le_refl _, zero_lt_one, fun k E η hE hη _ m _ => ?_⟩
              rw [heB _ _ hi]; simp; positivity
            obtain ⟨js, hjs⟩ := hA.2.2.2.2
            have Qs : Q js := by
              by_cases hb : js ∈ M.B
              · exact QB js hb
              have hθ : 0 < M.θ js := ((hA.2.2.2.1 js hb).2 hjs)
              have h1 := hsum1 js hb
              refine ⟨1, 1 - M.θ js, by linarith [hαnn js hb, Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => hαnn js hb l)], by linarith,
                fun k E η hE hη hH m hm => ?_⟩
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              have hb1 := hbound (k+m') js hb
              have h2 := hH.2 (k + m' + 1) (by omega) js hb
              have hg := hGen k E η hE hη hH m'
              have h3 : ∑ l, M.α js l * |e (k + m') l| ≤ (1 - M.θ js) * (m' * η + E) := by
                calc ∑ l, M.α js l * |e (k + m') l| ≤ ∑ l, M.α js l * (m' * η + E) :=
                      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hg l) (hαnn js hb l)
                  _ = (1 - M.θ js) * (m' * η + E) := by rw [← Finset.sum_mul]; congr 1; linarith
              show |e (k + m' + 1) js| ≤ _
              push_cast
              have : (1 - M.θ js) * (m' * η) ≤ m' * η := by
                have : 0 ≤ (m' : ℝ) * η := by positivity
                nlinarith
              nlinarith
            have Qstep : ∀ i j, adj i j → Q j → Q i := by
              intro i j hij hQj
              by_cases hi : i ∈ M.B
              · exact QB i hi
              have hα : 0 < M.α i j := (hA.2.1 i hi j).1 hij
              obtain ⟨m₀, ρ, hρ0, hρ1, hb⟩ := hQj
              have hαle : M.α i j ≤ 1 := by
                have := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hαnn i hi l) (Finset.mem_univ j)
                linarith [hsα i hi]
              refine ⟨m₀ + 1, 1 - M.α i j * (1 - ρ), ?_, ?_, fun k E η hE hη hH m hm => ?_⟩
              · nlinarith
              · nlinarith
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              have hb1 := hbound (k+m') i hi
              have h2 := hH.2 (k + m' + 1) (by omega) i hi
              have hg := hGen k E η hE hη hH m'
              have hj := hb k E η hE hη hH m' (by omega)
              have hsingle : M.α i j * (m' * η + E - |e (k + m') j|) ≤
                  ∑ l, M.α i l * (m' * η + E - |e (k + m') l|) :=
                Finset.single_le_sum (f := fun l => M.α i l * (m' * η + E - |e (k + m') l|))
                  (fun l _ => mul_nonneg (hαnn i hi l) (by linarith [hg l])) (Finset.mem_univ j)
              have hsplit : ∑ l, M.α i l * (m' * η + E - |e (k + m') l|) =
                  (∑ l, M.α i l) * (m' * η + E) - ∑ l, M.α i l * |e (k + m') l| := by
                rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun l _ => by ring
              have hmul : (∑ l, M.α i l) * (m' * η + E) ≤ m' * η + E :=
                mul_le_of_le_one_left (by positivity) (hsα i hi)
              have hk : M.α i j * ((1 - ρ) * E) ≤ M.α i j * (m' * η + E - |e (k + m') j|) :=
                mul_le_mul_of_nonneg_left (by linarith) hα.le
              show |e (k + m' + 1) i| ≤ _
              push_cast
              nlinarith
            have Qall : ∀ i, Q i := by
              intro i
              by_cases h : i = js
              · rw [h]; exact Qs
              · have htg := hA.2.2.1 i js h
                exact Relation.TransGen.head_induction_on htg (fun hij => Qstep _ _ hij Qs)
                  (fun hac _ hc => Qstep _ _ hac hc)
            choose m₀ ρ hρ0 hρ1 hQ using Qall
            obtain ⟨ρs, hρs0, hρs1, hρs⟩ : ∃ ρs : ℝ, 0 ≤ ρs ∧ ρs < 1 ∧ ∀ i, ρ i ≤ ρs := by
              rcases (Finset.univ : Finset (Fin n)).eq_empty_or_nonempty with h | h
              · exact ⟨0, le_refl _, zero_lt_one, fun i => absurd (Finset.mem_univ i) (by rw [h]; simp)⟩
              · obtain ⟨i0, _, hi0⟩ := Finset.exists_max_image Finset.univ ρ h
                exact ⟨ρ i0, hρ0 i0, hρ1 i0, fun i => hi0 i (Finset.mem_univ i)⟩
            set N : ℕ := ∑ i, m₀ i + 1 with hNdef
            have hC : ∀ k E η, 0 ≤ E → 0 ≤ η → H k E η → ∀ j, |e (k+N) j| ≤ N * η + ρs * E := by
              intro k E η hE hη hH j
              have hm : m₀ j ≤ N := by
                have := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => Nat.zero_le (m₀ l)) (Finset.mem_univ j)
                omega
              have := hQ j k E η hE hη hH N hm
              have : ρ j * E ≤ ρs * E := mul_le_mul_of_nonneg_right (hρs j) hE
              linarith
            have hδ : ∀ j ∉ M.B, Tendsto (fun l => δ l j) atTop (𝓝 0) := by
              intro j hj
              by_cases hθ : M.θ j = 0
              · simp only [δ, hθ, zero_mul]; exact tendsto_const_nhds
              · have hθp : 0 < M.θ j := lt_of_le_of_ne (hθnn j hj) (Ne.symm hθ)
                have hp := (hA.2.2.2.1 j hj).1 hθp
                have h1 := ((hP j hp).comp tendsto_natCast_atTop_atTop).sub_const t
                have h2 := h1.const_mul (M.θ j)
                simp only [sub_self, mul_zero] at h2
                exact h2
            have he0 : ∀ j, Tendsto (fun k => e k j) atTop (𝓝 0) := by
              intro j
              rw [Metric.tendsto_atTop]
              intro ε hε
              have hNpos : (0:ℝ) < N := by positivity
              set η := ε * (1 - ρs) / (4 * N) with hηdef
              have hη : 0 < η := by
                have : 0 < 1 - ρs := by linarith
                positivity
              have hev : ∀ᶠ l in atTop, ∀ j, j ∉ M.B → |δ l j| ≤ η := by
                rw [eventually_all]
                intro j
                by_cases hj : j ∉ M.B
                · filter_upwards [Metric.tendsto_nhds.1 (hδ j hj) η hη] with l hl
                  intro _
                  rw [Real.dist_eq, sub_zero] at hl
                  exact hl.le
                · exact Eventually.of_forall fun _ h => absurd h hj
              obtain ⟨k0, hk0⟩ := eventually_atTop.1 hev
              set E0 := ∑ j, |e k0 j| with hE0
              have hE0nn : 0 ≤ E0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
              have h1ρ : 0 < 1 - ρs := by linarith
              let F : ℕ → ℝ := fun s => ρs ^ s * E0 + N * η / (1 - ρs)
              have hFnn : ∀ s, 0 ≤ F s := fun s => by
                have : 0 ≤ ρs ^ s := pow_nonneg hρs0 s
                positivity
              have hHδ : ∀ k, k0 ≤ k → ∀ l, k < l → ∀ j ∉ M.B, |δ l j| ≤ η :=
                fun k hk l hl j hj => hk0 l (by omega) j hj
              have hiter : ∀ s, ∀ j, |e (k0 + s * N) j| ≤ F s := by
                intro s
                induction s with
                | zero =>
                  intro j
                  simp only [zero_mul, add_zero, F, pow_zero, one_mul]
                  have := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => abs_nonneg (e k0 l)) (Finset.mem_univ j)
                  have : 0 ≤ (N:ℝ) * η / (1 - ρs) := by positivity
                  linarith
                | succ s ih =>
                  intro j
                  have hk : k0 + (s + 1) * N = (k0 + s * N) + N := by ring
                  rw [hk]
                  have := hC (k0 + s * N) (F s) η (hFnn s) hη.le ⟨ih, hHδ _ (by omega)⟩ j
                  refine this.trans (le_of_eq ?_)
                  simp only [F]
                  field_simp
                  ring
              obtain ⟨t0, ht0⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * (E0 + 1)) by positivity) hρs1
              refine ⟨k0 + t0 * N, fun k hk => ?_⟩
              rw [Real.dist_eq, sub_zero]
              obtain ⟨s, hsdef⟩ : ∃ s, s = (k - k0) / N := ⟨_, rfl⟩
              obtain ⟨r, hrdef⟩ : ∃ r, r = (k - k0) % N := ⟨_, rfl⟩
              have hkdec : k = (k0 + s * N) + r := by
                have := Nat.div_add_mod' (k - k0) N
                rw [← hsdef, ← hrdef] at this
                omega
              have hNp : 0 < N := by omega
              have hs : t0 ≤ s := by
                rw [hsdef, Nat.le_div_iff_mul_le hNp]
                omega
              have hrN : r < N := hrdef ▸ Nat.mod_lt _ hNp
              have h1 := hGen (k0 + s * N) (F s) η (hFnn s) hη.le ⟨hiter s, hHδ _ (by omega)⟩ r j
              rw [← hkdec] at h1
              have hpow : ρs ^ s ≤ ρs ^ t0 := pow_le_pow_of_le_one hρs0 hρs1.le hs
              have hA1 : ρs ^ s * E0 < ε / 2 := by
                have : ρs ^ t0 * (E0 + 1) < ε / 2 := by
                  rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2 * (E0 + 1))] at ht0
                  linarith
                have : ρs ^ s * E0 ≤ ρs ^ t0 * (E0 + 1) := by
                  have : 0 ≤ ρs ^ s := pow_nonneg hρs0 s
                  nlinarith
                linarith
              have hA2 : (N:ℝ) * η / (1 - ρs) = ε / 4 := by
                rw [hηdef]; field_simp
              have hA3 : (r:ℝ) * η ≤ ε / 4 := by
                have : (r:ℝ) ≤ N := by exact_mod_cast hrN.le
                have : (r:ℝ) * η ≤ N * η := mul_le_mul_of_nonneg_right this hη.le
                have : (N:ℝ) * η = ε * (1 - ρs) / 4 := by rw [hηdef]; field_simp
                nlinarith
              simp only [F] at h1
              linarith
            have hgl : ∀ j, Tendsto (fun k => g k j) atTop (𝓝 t) := by
              intro j
              have := (he0 j).add_const t
              simp only [zero_add] at this
              refine this.congr fun k => ?_
              simp [e]
            have hidx : Tendsto (fun T : ℝ => ⌈T⌉₊ - 1) atTop atTop :=
              (tendsto_sub_atTop_nat 1).comp tendsto_nat_ceil_atTop
            rw [tendsto_pi_nhds]
            intro i
            by_cases hi : i ∈ M.B
            · simp only [beliefR, if_pos hi]
              exact tendsto_const_nhds
            have hθP : Tendsto (fun T : ℝ => M.θ i * personalR M y (fun _ => false) ω i T) atTop (𝓝 (M.θ i * t)) := by
              by_cases hθ : M.θ i = 0
              · simp only [hθ, zero_mul]; exact tendsto_const_nhds
              · have hθp : 0 < M.θ i := lt_of_le_of_ne (hθnn i hi) (Ne.symm hθ)
                exact (hP i ((hA.2.2.2.1 i hi).1 hθp)).const_mul _
            have hsl : Tendsto (fun T : ℝ => ∑ j, M.α i j * g (⌈T⌉₊ - 1) j) atTop (𝓝 (∑ j, M.α i j * t)) :=
              tendsto_finsetSum _ fun j _ => ((hgl j).comp hidx).const_mul _
            have hlim := hθP.add hsl
            have heq : M.θ i * t + ∑ j, M.α i j * t = t := by
              rw [← Finset.sum_mul]; linear_combination t * hsum1 i hi
            rw [heq] at hlim
            refine hlim.congr' ?_
            filter_upwards [eventually_gt_atTop 0] with T hT
            simp only [beliefR, if_neg hi, if_neg (not_le.2 hT), g]
          have hqclock : Measure.QuasiMeasurePreserving (fun ω : Sample n => ω.2.1) (sampleMeasure M y)
              (Measure.infinitePi fun _ : ℕ => expMeasure 1) := by
            unfold sampleMeasure
            exact Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
          have hqmarks : Measure.QuasiMeasurePreserving (fun ω : Sample n => ω.1) (sampleMeasure M y)
              (Measure.infinitePi fun k : Fin n × ℕ =>
                bernoulliMeasure State.S State.R (clampProb (organicProbS (M.p k.1) y))) := by
            unfold sampleMeasure
            exact Measure.quasiMeasurePreserving_fst
          have hA0 : ∀ᵐ e ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1), ∀ l, 0 ≤ e l :=
            ae_all_iff.2 fun l => (measurePreserving_eval_infinitePi _ l).quasiMeasurePreserving.ae hexp0
          have hB0 := slln (fun _ : ℕ => expMeasure 1) id (fun a b h => h) (fun _ => rfl)
            (fun x : ℝ => if 1 < x then (1:ℝ) else 0)
            (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)
            (fun x => by split_ifs <;> simp)
          have hclock : ∀ᵐ e ∂(Measure.infinitePi fun _ : ℕ => expMeasure 1), (∀ l, 0 ≤ e l) ∧
              Tendsto (fun N => ∑ l ∈ Finset.range N, e l) atTop atTop := by
            filter_upwards [hA0, hB0] with e h0 h1
            refine ⟨h0, ?_⟩
            have h2 : Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if 1 < e (id l) then (1:ℝ) else 0)) / N
                * (N : ℝ)) atTop atTop :=
              Tendsto.pos_mul_atTop hexpmean h1 tendsto_natCast_atTop_atTop
            have h3 : Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if 1 < e (id l) then (1:ℝ) else 0)))
                atTop atTop := by
              refine h2.congr' ?_
              rw [EventuallyEq, eventually_atTop]
              refine ⟨1, fun N hN => ?_⟩
              have : (N : ℝ) ≠ 0 := by positivity
              field_simp
            refine tendsto_atTop_mono (fun N => Finset.sum_le_sum fun l _ => ?_) h3
            simp only [id]
            split_ifs with h
            · exact h.le
            · exact h0 l
          have hmarks : ∀ i, ∀ᵐ m ∂(Measure.infinitePi fun k : Fin n × ℕ =>
                bernoulliMeasure State.S State.R (clampProb (organicProbS (M.p k.1) y))),
              Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if m (i, l) = y then (1:ℝ) else -1)) / N)
                atTop (𝓝 (2 * M.p i - 1)) := by
            intro i
            have := slln (fun k : Fin n × ℕ =>
                bernoulliMeasure State.S State.R (clampProb (organicProbS (M.p k.1) y)))
              (fun l => (i, l)) (fun a b h => by simpa using h) (fun _ => rfl)
              (fun s => if s = y then (1:ℝ) else -1) (Measurable.of_discrete) (fun s => by split_ifs <;> simp)
            rw [hber i] at this
            exact this
          have hAe := hqclock.ae hclock
          have hCe : ∀ᵐ ω ∂(sampleMeasure M y), ∀ i, 1/2 < M.p i →
              Tendsto (fun N : ℕ => (∑ l ∈ Finset.range N, (if ω.1 (i, l) = y then (1:ℝ) else -1)) / N)
                atTop (𝓝 (2 * M.p i - 1)) :=
            ae_all_iff.2 fun i => ((hqmarks.ae (hmarks i))).mono fun ω h _ => h
          filter_upwards [hAe, hCe] with ω h1 h2
          exact hdet ω (fun i hi => hPers ω h1.1 h1.2 i hi (h2 i hi))
