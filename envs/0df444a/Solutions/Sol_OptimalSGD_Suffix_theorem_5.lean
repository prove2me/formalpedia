-- Prove2me | solution 1 for OptimalSGD.Suffix.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T15:02:11.200005+00:00
-- url     : https://prove2.me/submissions/6d3ab9e0-b3bf-4aef-9207-eb0488de6dcd

/-
SPDX-License-Identifier: Apache-2.0
Full native suffix-averaged stochastic gradient descent theorem.
Mathematical source: Rakhlin, Shamir, Sridharan, Making Gradient Descent
Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7,
Theorem 5 and Appendices B.1, B.2, B.6.
Fresh native projection, relative strong-convex geometry, finite-product
Fubini and actual sampled-oracle moment proof. A stronger intermediate
suffix telescope is weakened to the unchanged published target constant.
All source hypotheses and finite-expectation obligations are preserved.
No accepted proof implementation is copied.
-/
import Mathlib
import Definitions.Def_OptimalSGD_Suffix_Model

-- BEGIN Foundation
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal
-- END Foundation

-- BEGIN Projection
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

variable {d : ℕ} {W : Set (Vec d)}

theorem projection_exists (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u : Vec d) : ∃ v, IsProjection W u v := by
  obtain ⟨v, hv, he⟩ := exists_norm_eq_iInf_of_complete_convex ⟨0, hW0⟩
    hWclosed.isComplete hWconv u
  refine ⟨v, hv, fun w hw => ?_⟩
  rw [norm_sub_rev v u, he, norm_sub_rev w u]
  have hb : BddBelow (Set.range (fun x : W => ‖u - (x : Vec d)‖)) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  exact ciInf_le hb ⟨w, hw⟩

theorem proj_spec (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u : Vec d) : IsProjection W u (projOnto W u) := by
  rw [projOnto, dif_pos (projection_exists hWconv hWclosed hW0 u)]
  exact Classical.choose_spec (projection_exists hWconv hWclosed hW0 u)

theorem proj_mem (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u : Vec d) : projOnto W u ∈ W :=
  (proj_spec hWconv hWclosed hW0 u).1

theorem proj_self (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) {u : Vec d} (hu : u ∈ W) : projOnto W u = u := by
  have h := (proj_spec hWconv hWclosed hW0 u).2 u hu
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using h

theorem proj_variational (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u : Vec d) {w : Vec d} (hw : w ∈ W) :
    ⟪u - projOnto W u, w - projOnto W u⟫_ℝ ≤ 0 := by
  have hs := proj_spec hWconv hWclosed hW0 u
  have : Nonempty W := ⟨⟨0, hW0⟩⟩
  have hb : BddBelow (Set.range (fun x : W => ‖u - (x : Vec d)‖)) :=
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩
  apply (norm_eq_iInf_iff_real_inner_le_zero hWconv hs.1).mp ?_ w hw
  apply le_antisymm
  · apply le_ciInf
    intro v
    simpa only [norm_sub_rev] using hs.2 v v.property
  · exact ciInf_le hb ⟨projOnto W u, hs.1⟩

theorem proj_nonexpansive (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u v : Vec d) :
    ‖projOnto W u - projOnto W v‖ ≤ ‖u - v‖ := by
  have h₁ := proj_variational hWconv hWclosed hW0 u
    (proj_mem hWconv hWclosed hW0 v)
  have h₂ := proj_variational hWconv hWclosed hW0 v
    (proj_mem hWconv hWclosed hW0 u)
  have hid : ‖projOnto W u - projOnto W v‖ ^ 2 ≤
      ⟪u - v, projOnto W u - projOnto W v⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right] at h₁ h₂ ⊢
    nlinarith [real_inner_comm (projOnto W u) (projOnto W v)]
  have hc := real_inner_le_norm (u-v) (projOnto W u-projOnto W v)
  nlinarith [norm_nonneg (projOnto W u-projOnto W v), norm_nonneg (u-v)]

theorem proj_dist_le (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) (u : Vec d) {w : Vec d} (hw : w ∈ W) :
    ‖projOnto W u - w‖ ≤ ‖u-w‖ := by
  simpa only [proj_self hWconv hWclosed hW0 hw] using
    proj_nonexpansive hWconv hWclosed hW0 u w

theorem continuous_proj (hWconv : Convex ℝ W) (hWclosed : IsClosed W)
    (hW0 : (0 : Vec d) ∈ W) : Continuous (projOnto W) := by
  have h : LipschitzWith 1 (projOnto W) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
      proj_nonexpansive hWconv hWclosed hW0 u v
  exact h.continuous

end SuffixSGDProof
-- END Projection

-- BEGIN Geometry
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

theorem squared_moment (D : Measure Z) [IsProbabilityMeasure D] (v : Z → Vec d)
    (hv : Integrable v D) {G : ℝ}
    (hm : ∫⁻ z, ENNReal.ofReal (‖v z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G^2)) :
    Integrable (fun z => ‖v z‖ ^ 2) D ∧ (∫ z, ‖v z‖ ^ 2 ∂D) ≤ G^2 := by
  have hs : AEStronglyMeasurable (fun z => ‖v z‖ ^ 2) D := hv.aestronglyMeasurable.norm.pow 2
  have hi : Integrable (fun z => ‖v z‖ ^ 2) D := by
    refine ⟨hs, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
      lt_of_le_of_lt hm ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _) hs]
  simpa only [ENNReal.toReal_ofReal (sq_nonneg G)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hm

theorem mean_norm_le (D : Measure Z) [IsProbabilityMeasure D] (v : Z → Vec d)
    (hv : Integrable v D) {G : ℝ}
    (hm : ∫⁻ z, ENNReal.ofReal (‖v z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G^2)) :
    ‖∫ z, v z ∂D‖ ≤ |G| := by
  have hi := squared_moment D v hv hm
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (by fun_prop) isClosed_Ici (Filter.Eventually.of_forall fun z => norm_nonneg (v z))
    hv.norm hi.1
  have hnorm := norm_integral_le_integral_norm v (μ := D)
  have hn : 0 ≤ ∫ z, ‖v z‖ ∂D := integral_nonneg fun z => norm_nonneg _
  have hsq : (∫ z, ‖v z‖ ∂D)^2 ≤ G^2 := hj.trans hi.2
  nlinarith [norm_nonneg (∫ z, v z ∂D), abs_nonneg G, sq_abs G]

theorem strong_subgradient {W : Set (Vec d)} {F : Vec d → ℝ} {lam : ℝ}
    (hF : StrongConvexOn W lam F) {w u v : Vec d} (hw : w ∈ W) (hu : u ∈ W)
    (hsub : ∀ z ∈ W, F w + ⟪z-w,v⟫_ℝ ≤ F z) :
    F w + ⟪u-w,v⟫_ℝ + lam/2*‖u-w‖^2 ≤ F u := by
  have hseg (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
      F w + ⟪u-w,v⟫_ℝ + lam/2*(1-t)*‖u-w‖^2 ≤ F u := by
    have hc := hF.2 hw hu (sub_nonneg.mpr ht1) ht.le (by ring : 1-t+t=1)
    have hs := hsub ((1-t) • w + t • u)
      (hF.1 hw hu (sub_nonneg.mpr ht1) ht.le (by ring))
    have he : (1-t) • w + t • u - w = t • (u-w) := by module
    rw [he] at hs
    simp only [inner_smul_left, starRingEnd_apply, star_trivial] at hs
    rw [norm_sub_rev w u] at hc
    simp only [smul_eq_mul] at hc
    apply (mul_le_mul_iff_left₀ ht).mp
    nlinarith
  have hh (n : ℕ) : F w + ⟪u-w,v⟫_ℝ + lam/2*(1-1/((n:ℝ)+1))*‖u-w‖^2 ≤ F u :=
    hseg _ (by positivity) (by rw [div_le_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have ht : Tendsto (fun n : ℕ => F w + ⟪u-w,v⟫_ℝ +
      lam/2*(1-1/((n:ℝ)+1))*‖u-w‖^2) atTop
      (𝓝 (F w + ⟪u-w,v⟫_ℝ + lam/2*‖u-w‖^2)) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h' := ((h.const_sub 1).const_mul (lam/2)).mul_const (‖u-w‖^2)
    simpa only [sub_zero, mul_one] using h'.const_add (F w + ⟪u-w,v⟫_ℝ)
  exact le_of_tendsto ht (Filter.Eventually.of_forall hh)

theorem minimizer_growth {W : Set (Vec d)} {F : Vec d → ℝ} {lam : ℝ}
    (hF : StrongConvexOn W lam F) {wstar w : Vec d} (hwstar : wstar ∈ W)
    (hmin : ∀ u ∈ W, F wstar ≤ F u) (hw : w ∈ W) :
    lam/2*‖w-wstar‖^2 ≤ F w-F wstar := by
  have h := strong_subgradient hF hwstar hw (v := 0) (by simpa using hmin)
  simpa only [inner_zero_right, add_zero, le_sub_iff_add_le, add_comm] using h

theorem objective_lipschitz {W : Set (Vec d)} {F : Vec d → ℝ}
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (ho : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g) {G : ℝ}
    (hm : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖^2) ∂D ≤ ENNReal.ofReal (G^2))
    {u w : Vec d} (hu : u ∈ W) (hw : w ∈ W) : |F u-F w| ≤ |G| *‖u-w‖ := by
  have hmu := mean_norm_le D (g u) (ho u hu).1 (hm u hu)
  have hmw := mean_norm_le D (g w) (ho w hw).1 (hm w hw)
  have h₁ := (ho u hu).2 w hw
  have h₂ := (ho w hw).2 u hu
  have c₁ := abs_real_inner_le_norm (w-u) (OptimalSGD.Suffix.oracleMean D g u)
  have c₂ := abs_real_inner_le_norm (u-w) (OptimalSGD.Suffix.oracleMean D g w)
  rw [norm_sub_rev w u] at c₁
  change ‖OptimalSGD.Suffix.oracleMean D g u‖ ≤ |G| at hmu
  change ‖OptimalSGD.Suffix.oracleMean D g w‖ ≤ |G| at hmw
  have b₁ := mul_le_mul_of_nonneg_left hmu (norm_nonneg (u-w))
  have b₂ := mul_le_mul_of_nonneg_left hmw (norm_nonneg (u-w))
  rw [abs_le] at c₁ c₂ ⊢
  constructor <;> nlinarith

theorem domain_bound {W : Set (Vec d)} {F : Vec d → ℝ} {lam G : ℝ}
    (hlam : 0<lam) (hF : StrongConvexOn W lam F) {wstar w : Vec d}
    (hwstar : wstar ∈ W) (hmin : ∀ u ∈ W, F wstar ≤ F u) (hw : w ∈ W)
    (hlip : |F w-F wstar| ≤ |G| *‖w-wstar‖) : ‖w-wstar‖ ≤ 2*|G|/lam := by
  have hg := minimizer_growth hF hwstar hmin hw
  rw [le_div_iff₀ hlam]
  have hh : F w-F wstar ≤ |G| *‖w-wstar‖ := (le_abs_self _).trans hlip
  by_cases hn : ‖w-wstar‖ = 0
  · simp only [hn, zero_mul]
    positivity
  · have hp : 0 < ‖w-wstar‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith

theorem continuous_objective_projection {W : Set (Vec d)} {F : Vec d → ℝ} {G : ℝ}
    (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (hlip : ∀ u ∈ W, ∀ w ∈ W, |F u-F w| ≤ |G| *‖u-w‖) :
    Continuous (fun x => F (projOnto W x)) := by
  have h : LipschitzWith ⟨|G|, abs_nonneg G⟩ (fun x => F (projOnto W x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro u w
    simp only [dist_eq_norm]
    exact (hlip _ (proj_mem hWconv hWclosed hW0 u) _ (proj_mem hWconv hWclosed hW0 w)).trans
      (mul_le_mul_of_nonneg_left (proj_nonexpansive hWconv hWclosed hW0 u w) (abs_nonneg G))
  exact h.continuous

end SuffixSGDProof
-- END Geometry

-- BEGIN ScalarRate
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

theorem distance_rate {A : ℝ} (hA : 0≤A) (D : ℕ→ℝ) (T : ℕ)
    (hn : ∀ t, 0≤D t) (hzero : D 0≤4*A)
    (hr : ∀ t<T, D (t+1)≤(1-2/((t:ℝ)+1))*D t+A/((t:ℝ)+1)^2) :
    ∀ t≤T, D t≤4*A/((t:ℝ)+1) := by
  intro t ht
  induction t with
  | zero => simpa using hzero
  | succ t ih =>
    have hrec := hr t (by omega)
    by_cases hz : t=0
    · subst t
      norm_num at hrec ⊢
      nlinarith [hn 0]
    · have ht1 : (1:ℝ)≤t := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      have hp : 0<(t:ℝ)+1 := by positivity
      have hcoef : 0≤1-2/((t:ℝ)+1) := by
        rw [sub_nonneg, div_le_one hp]; linarith
      have hi := mul_le_mul_of_nonneg_left (ih (by omega)) hcoef
      have halg : (1-2/((t:ℝ)+1))*(4*A/((t:ℝ)+1))+A/((t:ℝ)+1)^2 ≤
          4*A/((t:ℝ)+2) := by
        field_simp
        nlinarith [mul_nonneg hA (show 0≤3*(t:ℝ)+10 by positivity)]
      simp only [Nat.cast_add, Nat.cast_one] at ⊢
      calc
        D (t+1) ≤ (1-2/((t:ℝ)+1))*D t+A/((t:ℝ)+1)^2 := hrec
        _ ≤ (1-2/((t:ℝ)+1))*(4*A/((t:ℝ)+1))+A/((t:ℝ)+1)^2 := by linarith
        _ ≤ 4*A/((t:ℝ)+1+1) := by convert halg using 1; ring

theorem reciprocal_log_increment {n : ℕ} (hn : 0<n) :
    1/((n:ℝ)+1)≤Real.log ((n:ℝ)+1)-Real.log n := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (div_pos hp (by positivity : 0<(n:ℝ)+1))
  rw [Real.log_div (ne_of_gt hp) (by positivity)] at h
  have he : (n:ℝ)/((n:ℝ)+1)-1 = -(1/((n:ℝ)+1)) := by field_simp; ring
  rw [he] at h
  linarith

theorem harmonic_bound (k T : ℕ) (hk : 0<k) (hkT : k≤T) :
    (∑ t ∈ Finset.Ico k T, 1/((t:ℝ)+1))≤Real.log T-Real.log k := by
  induction T, hkT using Nat.le_induction with
  | base => simp
  | succ T hT ih =>
    rw [Finset.sum_Ico_succ_top hT]
    have hi := reciprocal_log_increment (lt_of_lt_of_le hk hT)
    simpa only [Nat.cast_add, Nat.cast_one] using add_le_add ih hi |>.trans_eq (by ring)

theorem suffix_scalar {lam A : ℝ} (hlam : 0<lam) (hA : 0≤A)
    (D L : ℕ→ℝ) (k T : ℕ) (hk : 0<k) (hkT : k<T)
    (hn : ∀ t, 0≤D t) (hD : D k≤4*A/(lam^2*((k:ℝ)+1)))
    (hstep : ∀ t∈Finset.Ico k T,
      2*L t≤lam*t*D t-lam*(t+1)*D (t+1)+A/(lam*(t+1))) :
    (∑ t∈Finset.Ico k T, L t)≤A/lam*(2+(Real.log T-Real.log k)/2) := by
  have hs := Finset.sum_le_sum hstep
  have htelescope : (∑ t∈Finset.Ico k T,
      (lam*(t:ℝ)*D t-lam*((t:ℝ)+1)*D (t+1))) = lam*k*D k-lam*T*D T := by
    simpa only [Nat.cast_add, Nat.cast_one, neg_mul, neg_sub_neg] using
      Finset.sum_Ico_sub (fun t : ℕ => -(lam*(t:ℝ)*D t)) hkT.le
  have hnorm : (∑ t∈Finset.Ico k T, A/(lam*((t:ℝ)+1))) =
      A/lam*(∑ t∈Finset.Ico k T, 1/((t:ℝ)+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [div_mul_eq_div_div, one_div]
    ring
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  rw [htelescope, hnorm] at hs
  have hinit : lam*k*D k≤4*A/lam := by
    have hi := mul_le_mul_of_nonneg_left hD (by positivity : 0≤lam*(k:ℝ))
    have hb : lam*k*(4*A/(lam^2*((k:ℝ)+1)))≤4*A/lam := by
      field_simp
      nlinarith
    exact hi.trans hb
  have hterm : 0≤lam*T*D T := mul_nonneg (by positivity) (hn T)
  have hH := mul_le_mul_of_nonneg_left (harmonic_bound k T hk hkT.le)
    (div_nonneg hA hlam.le)
  have he : 4*A/lam=4*(A/lam) := by ring
  rw [he] at hinit
  nlinarith

end SuffixSGDProof
-- END ScalarRate

-- BEGIN Averaging
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

variable {d : ℕ}

theorem average_mem {W : Set (Vec d)} (hW : Convex ℝ W) (w : ℕ→Vec d)
    (k T : ℕ) (hkT : k<T) (hw : ∀ t∈Finset.Ico k T, w t∈W) :
    (((T-k:ℕ):ℝ)⁻¹ • ∑ t∈Finset.Ico k T, w t)∈W := by
  have hn : ((T-k:ℕ):ℝ)≠0 := by exact_mod_cast Nat.sub_ne_zero_of_lt hkT
  have hh := hW.sum_mem (t := Finset.Ico k T) (w := fun _ => ((T-k:ℕ):ℝ)⁻¹)
    (by intros; positivity) (by simp [hn]) hw
  simpa only [← Finset.smul_sum] using hh

theorem average_jensen {W : Set (Vec d)} {F : Vec d→ℝ} (hF : ConvexOn ℝ W F)
    (w : ℕ→Vec d) (k T : ℕ) (hkT : k<T) (hw : ∀ t∈Finset.Ico k T, w t∈W) :
    F (((T-k:ℕ):ℝ)⁻¹ • ∑ t∈Finset.Ico k T, w t)≤
      ((T-k:ℕ):ℝ)⁻¹ * ∑ t∈Finset.Ico k T, F (w t) := by
  have hn : ((T-k:ℕ):ℝ)≠0 := by exact_mod_cast Nat.sub_ne_zero_of_lt hkT
  have hh := hF.map_sum_le (t := Finset.Ico k T) (w := fun _ => ((T-k:ℕ):ℝ)⁻¹)
    (by intros; positivity) (by simp [hn]) hw
  simpa only [← Finset.smul_sum, smul_eq_mul, ← Finset.mul_sum] using hh

theorem integral_average_gap {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Vec d→ℝ) (w : ℕ→Ω→Vec d) (wstar : Vec d)
    (k T : ℕ) (hkT : k<T)
    (ha : Integrable (fun S => F (((T-k:ℕ):ℝ)⁻¹ • ∑ t∈Finset.Ico k T, w t S)) μ)
    (hi : ∀ t∈Finset.Ico k T, Integrable (fun S => F (w t S)) μ)
    (hj : ∀ S, F (((T-k:ℕ):ℝ)⁻¹ • ∑ t∈Finset.Ico k T, w t S)≤
      ((T-k:ℕ):ℝ)⁻¹ * ∑ t∈Finset.Ico k T, F (w t S)) :
    (∫ S, (F (((T-k:ℕ):ℝ)⁻¹ • ∑ t∈Finset.Ico k T, w t S)-F wstar) ∂μ)≤
      ((T-k:ℕ):ℝ)⁻¹ * ∑ t∈Finset.Ico k T, ∫ S, (F (w t S)-F wstar) ∂μ := by
  have h := integral_mono ha ((integrable_finsetSum _ hi).const_mul _) hj
  rw [integral_const_mul, integral_finsetSum _ hi] at h
  rw [integral_sub ha (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  have he : (∑ t∈Finset.Ico k T, ∫ S, (F (w t S)-F wstar) ∂μ)=
      (∑ t∈Finset.Ico k T, ∫ S, F (w t S) ∂μ)-((T-k:ℕ):ℝ)*F wstar := by
    calc
      _ = ∑ t∈Finset.Ico k T, ((∫ S, F (w t S) ∂μ)-F wstar) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [integral_sub (hi t ht) (integrable_const _)]
        simp
      _ = _ := by simp [Finset.sum_sub_distrib]
  rw [he]
  have hn : ((T-k:ℕ):ℝ)≠0 := by exact_mod_cast Nat.sub_ne_zero_of_lt hkT
  have he' : ((T-k:ℕ):ℝ)⁻¹ *
      ((∑ t∈Finset.Ico k T, ∫ S, F (w t S) ∂μ)-((T-k:ℕ):ℝ)*F wstar)=
      ((T-k:ℕ):ℝ)⁻¹*(∑ t∈Finset.Ico k T, ∫ S, F (w t S) ∂μ)-F wstar := by
    field_simp
  rw [he']
  linarith

end SuffixSGDProof
-- END Averaging

-- BEGIN RunMeasurable
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

open OptimalSGD.Suffix

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem run_mem (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d)
    (h0 : (0 : Vec d) ∈ W) (hp : ∀ v, projOnto W v ∈ W)
    {T : ℕ} (S : Fin T → Z) (t : ℕ) :
    sgdStrongIterates lam W g S t ∈ W := by
  cases t with
  | zero => exact h0
  | succ t => exact hp _

theorem measurable_run (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d)
    (hp : Continuous (projOnto W)) (hg : Measurable (Function.uncurry g))
    (T t : ℕ) : Measurable (fun S : Fin T → Z => sgdStrongIterates lam W g S t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [sgdStrongIterates]
    apply hp.measurable.comp
    by_cases ht : t < T
    · simp only [dif_pos ht]
      have hgg : Measurable (fun S : Fin T → Z =>
          g (sgdStrongIterates lam W g S t) (S ⟨t, ht⟩)) := by
        have heval : Measurable (fun S : Fin T → Z => S ⟨t, ht⟩) :=
          measurable_pi_apply (⟨t, ht⟩ : Fin T)
        simpa only [Function.comp_def, Function.uncurry] using hg.comp (ih.prodMk heval)
      exact ih.sub (hgg.const_smul (1 / (lam * ((t : ℝ) + 1))))
    · simp only [dif_neg ht, smul_zero, sub_zero]
      exact ih

omit [MeasurableSpace Z] in
theorem run_eq_of_past_eq (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d)
    {T : ℕ} (S S' : Fin T → Z) (t : ℕ)
    (h : ∀ i : Fin T, (i : ℕ) < t → S i = S' i) :
    sgdStrongIterates lam W g S t = sgdStrongIterates lam W g S' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun i hi => h i (by omega))
    simp only [sgdStrongIterates, he]
    by_cases ht : t < T
    · simp only [dif_pos ht, h ⟨t, ht⟩ (by simp)]
    · simp only [dif_neg ht]

omit [MeasurableSpace Z] in
theorem run_update_current (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d)
    {T : ℕ} (S : Fin T → Z) (i : Fin T) (z : Z) :
    sgdStrongIterates lam W g (Function.update S i z) i =
      sgdStrongIterates lam W g S i := by
  classical
  apply run_eq_of_past_eq
  intro j hj
  have hji : j ≠ i := by intro h; subst j; exact (lt_irrefl _ hj)
  exact Function.update_of_ne hji _ _

theorem measurable_suffix (lam : ℝ) (W : Set (Vec d)) (g : Vec d → Z → Vec d)
    (hp : Continuous (projOnto W)) (hg : Measurable (Function.uncurry g))
    (T k : ℕ) : Measurable (fun S : Fin T → Z => suffixAverage lam W g S k) := by
  unfold suffixAverage
  exact (Finset.measurable_sum _ fun t _ => measurable_run lam W g hp hg T t).const_smul (((T - k : ℕ) : ℝ)⁻¹)

end SuffixSGDProof
-- END RunMeasurable

-- BEGIN ProductMoments
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

instance iid_probability (D : Measure Z) [IsProbabilityMeasure D] (T : ℕ) :
    IsProbabilityMeasure (iidLaw D T) := by
  unfold iidLaw
  infer_instance

theorem moment_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Vec d) (hf : Measurable f) (C : ℝ)
    (hC : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun x => ‖f x‖ ^ 2) μ ∧ ∫ x, ‖f x‖ ^ 2 ∂μ ≤ max C 0 := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) μ := by
    refine ⟨(hf.norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖)]
    exact hC.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖)
  rw [← he] at hC
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)).mp
    (hC.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0)))

theorem coordinate_moments (D : Measure Z) [IsProbabilityMeasure D]
    {n : ℕ} (i : Fin (n + 1)) (w : (Fin (n + 1) → Z) → Vec d)
    (hw : Measurable w) (hi : ∀ S z, w (Function.update S i z) = w S)
    (g : Vec d → Z → Vec d) (hg : Measurable (Function.uncurry g))
    (W : Set (Vec d)) (hW : ∀ S, w S ∈ W)
    (hgi : ∀ x ∈ W, Integrable (g x) D) (C : ℝ)
    (hm : ∀ x ∈ W, ∫⁻ z, ENNReal.ofReal (‖g x z‖ ^ 2) ∂D ≤ ENNReal.ofReal C)
    (a : Vec d) (R : ℝ) (hR : 0 ≤ R) (hb : ∀ S, ‖w S - a‖ ≤ R) :
    Integrable (fun S => ‖g (w S) (S i)‖ ^ 2) (iidLaw D (n + 1)) ∧
    (∫ S, ‖g (w S) (S i)‖ ^ 2 ∂iidLaw D (n + 1)) ≤ max C 0 ∧
    Integrable (fun S => ⟪g (w S) (S i), w S - a⟫_ℝ) (iidLaw D (n + 1)) ∧
    Integrable (fun S => ⟪∫ z, g (w S) z ∂D, w S - a⟫_ℝ) (iidLaw D (n + 1)) ∧
    (∫ S, ⟪g (w S) (S i), w S - a⟫_ℝ ∂iidLaw D (n + 1)) =
      ∫ S, ⟪∫ z, g (w S) z ∂D, w S - a⟫_ℝ ∂iidLaw D (n + 1) := by
  classical
  have : Nonempty Z := nonempty_of_isProbabilityMeasure D
  let z0 : Z := Classical.choice inferInstance
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Z) i).symm
  let μ : Measure (Fin n → Z) := Measure.pi (fun _ => D)
  have he : MeasurePreserving e (D.prod μ) (iidLaw D (n + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => D) i).symm
  let v : (Fin n → Z) → Vec d := fun r => w (e (z0, r))
  have hv : Measurable v := hw.comp (e.measurable.comp (measurable_const.prodMk measurable_id))
  have hwe (z : Z) (r : Fin n → Z) : w (e (z, r)) = v r := by
    have h := hi (i.insertNth z0 r) z
    simpa only [e, v, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.update_insertNth] using h
  have hei (z : Z) (r : Fin n → Z) : e (z, r) i = z := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply]
  have hwep (p : Z × (Fin n → Z)) : w (e p) = v p.2 := hwe p.1 p.2
  have heip (p : Z × (Fin n → Z)) : e p i = p.1 := hei p.1 p.2
  have hvW (r : Fin n → Z) : v r ∈ W := hW _
  have hgm : Measurable (fun p : Z × (Fin n → Z) => g (v p.2) p.1) :=
    hg.comp ((hv.comp measurable_snd).prodMk measurable_fst)
  have hlow : (∫⁻ p : Z × (Fin n → Z),
      ENNReal.ofReal (‖g (v p.2) p.1‖ ^ 2) ∂D.prod μ) ≤ ENNReal.ofReal C := by
    rw [lintegral_prod_symm _ (hgm.norm.pow_const 2).ennreal_ofReal.aemeasurable]
    calc
      _ ≤ ∫⁻ _ : Fin n → Z, ENNReal.ofReal C ∂μ :=
        lintegral_mono fun r => hm (v r) (hvW r)
      _ = _ := by simp [μ]
  have hglow : (∫⁻ S, ENNReal.ofReal (‖g (w S) (S i)‖ ^ 2)
      ∂iidLaw D (n + 1)) ≤ ENNReal.ofReal C := by
    rw [← he.lintegral_comp_emb e.measurableEmbedding]
    simpa only [Function.comp_def, hwep, heip] using hlow
  have hgs : Measurable (fun S => g (w S) (S i)) :=
    hg.comp (hw.prodMk (measurable_pi_apply i))
  obtain ⟨hgsq, hgsqle⟩ := moment_integrable (iidLaw D (n + 1)) _ hgs C hglow
  have hmixm : Measurable (fun S => ⟪g (w S) (S i), w S - a⟫_ℝ) :=
    hgs.inner (hw.sub measurable_const)
  have hmix : Integrable (fun S => ⟪g (w S) (S i), w S - a⟫_ℝ)
      (iidLaw D (n + 1)) := by
    apply ((integrable_const (1 : ℝ)).add hgsq).const_mul R |>.mono'
      hmixm.aestronglyMeasurable
    filter_upwards [] with S
    rw [Real.norm_eq_abs]
    calc
      |⟪g (w S) (S i), w S - a⟫_ℝ| ≤ ‖g (w S) (S i)‖ * ‖w S - a‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖g (w S) (S i)‖ * R := mul_le_mul_of_nonneg_left (hb S) (norm_nonneg _)
      _ ≤ R * (1 + ‖g (w S) (S i)‖ ^ 2) := by
        nlinarith [sq_nonneg (‖g (w S) (S i)‖ - 1)]
  have hpull : Integrable (fun p : Z × (Fin n → Z) =>
      ⟪g (v p.2) p.1, v p.2 - a⟫_ℝ) (D.prod μ) := by
    have h := he.integrable_comp_of_integrable hmix
    simpa only [Function.comp_def, hwep, heip] using h
  have hfiber (r : Fin n → Z) :
      (∫ z, ⟪g (v r) z, v r - a⟫_ℝ ∂D) =
        ⟪∫ z, g (v r) z ∂D, v r - a⟫_ℝ := by
    simpa only [real_inner_comm] using integral_inner (𝕜 := ℝ) (hgi (v r) (hvW r)) (v r - a)
  have hmeanr : Integrable (fun r => ⟪∫ z, g (v r) z ∂D, v r - a⟫_ℝ) μ := by
    have h := hpull.integral_prod_right
    simpa only [hfiber] using h
  have hmeanpull : Integrable (fun p : Z × (Fin n → Z) =>
      ⟪∫ z, g (v p.2) z ∂D, v p.2 - a⟫_ℝ) (D.prod μ) :=
    hmeanr.comp_snd D
  have hmean : Integrable (fun S => ⟪∫ z, g (w S) z ∂D, w S - a⟫_ℝ)
      (iidLaw D (n + 1)) := by
    rw [← he.integrable_comp_emb e.measurableEmbedding]
    simpa only [Function.comp_def, hwep] using hmeanpull
  refine ⟨hgsq, hgsqle, hmix, hmean, ?_⟩
  rw [← he.integral_comp', ← he.integral_comp']
  simp only [hwep, heip]
  rw [integral_prod_symm _ hpull, integral_prod_symm _ hmeanpull]
  simp only [hfiber, integral_const, probReal_univ, one_smul]

end SuffixSGDProof
-- END ProductMoments

-- BEGIN ExpectedStep
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace SuffixSGDProof

open OptimalSGD.Suffix

variable {d : ℕ} {Z : Type*} [MeasurableSpace Z]

omit [MeasurableSpace Z] in
theorem bounded_objective_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Set (Vec d)} {F : Vec d → ℝ}
    (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    {G R : ℝ} {a : Vec d} (ha : a ∈ W)
    (hlip : ∀ u ∈ W, ∀ v ∈ W, |F u - F v| ≤ |G| * ‖u - v‖)
    (hR : ∀ u ∈ W, ‖u - a‖ ≤ R)
    (w : Ω → Vec d) (hw : Measurable w) (hmem : ∀ s, w s ∈ W) :
    Integrable (fun s => F (w s)) μ ∧
    Integrable (fun s => ‖w s - a‖ ^ 2) μ := by
  have hf : Measurable (fun s => F (w s)) := by
    have h := (continuous_objective_projection hWconv hWclosed hW0 hlip).measurable.comp hw
    change Measurable (fun s => F (projOnto W (w s))) at h
    have he : (fun s => F (projOnto W (w s))) = (fun s => F (w s)) := by
      funext s
      rw [proj_self hWconv hWclosed hW0 (hmem s)]
    rw [he] at h
    exact h
  constructor
  · apply (integrable_const (|F a| + |G| * R)).mono' hf.aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_eq_abs]
    have h := (hlip (w s) (hmem s) a ha).trans
      (mul_le_mul_of_nonneg_left (hR (w s) (hmem s)) (abs_nonneg G))
    calc
      |F (w s)| = |(F (w s) - F a) + F a| := by congr 1; ring
      _ ≤ |F (w s) - F a| + |F a| := abs_add_le _ _
      _ ≤ _ := by linarith
  · apply (integrable_const (R ^ 2)).mono' ((hw.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hR (w s) (hmem s))) |>.2
      (hR (w s) (hmem s))

theorem run_integrable (W : Set (Vec d)) (hWconv : Convex ℝ W)
    (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (ho : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hm : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (a : Vec d) (ha : a ∈ W) (hmin : ∀ w ∈ W, F a ≤ F w) (T t : ℕ) :
    Integrable (fun S : Fin T → Z => F (sgdStrongIterates lam W g S t)) (iidLaw D T) ∧
    Integrable (fun S : Fin T → Z => ‖sgdStrongIterates lam W g S t - a‖ ^ 2) (iidLaw D T) := by
  apply bounded_objective_integrable (iidLaw D T) hWconv hWclosed hW0 ha
    (fun u hu v hv => objective_lipschitz D g ho hm hu hv)
    (fun u hu => domain_bound hlam hF ha hmin hu (objective_lipschitz D g ho hm hu ha))
  · exact measurable_run lam W g (continuous_proj hWconv hWclosed hW0) hg T t
  · exact fun S => run_mem lam W g hW0 (proj_mem hWconv hWclosed hW0) S t

theorem expected_recurrences (W : Set (Vec d)) (hWconv : Convex ℝ W)
    (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (ho : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hm : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (a : Vec d) (ha : a ∈ W) (hmin : ∀ w ∈ W, F a ≤ F w)
    (T t : ℕ) (ht : t < T) :
    (∫ S, ‖sgdStrongIterates lam W g S (t + 1) - a‖ ^ 2 ∂iidLaw D T) ≤
      (1 - 2 / ((t : ℝ) + 1)) *
        (∫ S, ‖sgdStrongIterates lam W g S t - a‖ ^ 2 ∂iidLaw D T) +
        G ^ 2 / (lam ^ 2 * ((t : ℝ) + 1) ^ 2) ∧
    2 * (∫ S, (F (sgdStrongIterates lam W g S t) - F a) ∂iidLaw D T) ≤
      lam * t * (∫ S, ‖sgdStrongIterates lam W g S t - a‖ ^ 2 ∂iidLaw D T) -
      lam * (t + 1) * (∫ S, ‖sgdStrongIterates lam W g S (t + 1) - a‖ ^ 2 ∂iidLaw D T) +
      G ^ 2 / (lam * (t + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show T ≠ 0 by omega)
  let i : Fin (n + 1) := ⟨t, ht⟩
  let w (s : ℕ) (S : Fin (n + 1) → Z) := sgdStrongIterates lam W g S s
  let η : ℝ := 1 / (lam * (t + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hmem (s : ℕ) (S : Fin (n + 1) → Z) : w s S ∈ W :=
    run_mem lam W g hW0 (proj_mem hWconv hWclosed hW0) S s
  have hw : Measurable (w t) :=
    measurable_run lam W g (continuous_proj hWconv hWclosed hW0) hg _ _
  have hii (s : ℕ) := run_integrable W hWconv hWclosed hW0 F hlam hF D g hg ho hm a ha hmin (n + 1) s
  have hq (s : ℕ) : Integrable (fun S => ‖w s S - a‖ ^ 2) (iidLaw D (n + 1)) := (hii s).2
  have hf : Integrable (fun S => F (w t S) - F a) (iidLaw D (n + 1)) :=
    (hii t).1.sub (integrable_const _)
  obtain ⟨hgq, hgql, hmix, hmean, heq⟩ := coordinate_moments D i (w t) hw
    (fun S z => run_update_current lam W g S i z) g hg W (hmem t)
    (fun x hx => (ho x hx).1) (G ^ 2) hm a (2 * |G| / lam) (by positivity)
    (fun S => domain_bound hlam hF ha hmin (hmem t S)
      (objective_lipschitz D g ho hm (hmem t S) ha))
  rw [max_eq_left (sq_nonneg G)] at hgql
  have hpoint (S : Fin (n + 1) → Z) :
      ‖w (t + 1) S - a‖ ^ 2 ≤
        ‖w t S - a‖ ^ 2 - 2 * η * ⟪g (w t S) (S i), w t S - a⟫_ℝ +
          η ^ 2 * ‖g (w t S) (S i)‖ ^ 2 := by
    have hp := proj_dist_le hWconv hWclosed hW0 (w t S - η • g (w t S) (S i)) ha
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hp
    change ‖projOnto W (w t S - η • g (w t S) (S i)) - a‖ ^ 2 ≤ _ at hs
    have he : w t S - η • g (w t S) (S i) - a = (w t S - a) - η • g (w t S) (S i) := by module
    rw [he, norm_sub_sq_real (w t S - a) (η • g (w t S) (S i)), inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs] at hs
    simpa only [w, sgdStrongIterates, dif_pos ht, η, i, real_inner_comm, mul_assoc] using hs
  have hb := integral_mono (hq (t + 1))
    (((hq t).sub (hmix.const_mul (2 * η))).add (hgq.const_mul (η ^ 2))) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [integral_add (f := fun S => ‖w t S - a‖ ^ 2 - 2 * η * ⟪g (w t S) (S i), w t S - a⟫_ℝ)
      (g := fun S => η ^ 2 * ‖g (w t S) (S i)‖ ^ 2)
      ((hq t).sub (hmix.const_mul (2 * η))) (hgq.const_mul (η ^ 2)),
    integral_sub (hq t) (hmix.const_mul (2 * η)), integral_const_mul, integral_const_mul,
    heq] at hb
  have hgqlη := mul_le_mul_of_nonneg_left hgql (sq_nonneg η)
  have hb' :
      (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) ≤
      (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) -
      2 * η * (∫ S, ⟪∫ z, g (w t S) z ∂D, w t S - a⟫_ℝ ∂iidLaw D (n + 1)) +
      η ^ 2 * G ^ 2 := by linarith
  have hstrong (S : Fin (n + 1) → Z) :
      F (w t S) - F a + lam / 2 * ‖w t S - a‖ ^ 2 ≤
        ⟪∫ z, g (w t S) z ∂D, w t S - a⟫_ℝ := by
    have h := strong_subgradient hF (hmem t S) ha (ho (w t S) (hmem t S)).2
    change F (w t S) + ⟪a - w t S, ∫ z, g (w t S) z ∂D⟫_ℝ +
      lam / 2 * ‖a - w t S‖ ^ 2 ≤ F a at h
    rw [norm_sub_rev, inner_sub_left] at h
    rw [inner_sub_right, real_inner_comm (w t S) (∫ z, g (w t S) z ∂D),
      real_inner_comm a (∫ z, g (w t S) z ∂D)]
    linarith
  have hs := integral_mono (hf.add ((hq t).const_mul (lam / 2))) hmean hstrong
  simp only [Pi.add_apply] at hs
  rw [integral_add (f := fun S => F (w t S) - F a)
    (g := fun S => lam / 2 * ‖w t S - a‖ ^ 2) hf ((hq t).const_mul (lam / 2)), integral_const_mul] at hs
  have hgr := integral_mono ((hq t).const_mul (lam / 2)) hf
    (fun S => minimizer_growth hF ha hmin (hmem t S))
  rw [integral_const_mul] at hgr
  have hsη := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * η by positivity)
  have hgrη := mul_le_mul_of_nonneg_left hgr (show 0 ≤ 2 * η by positivity)
  have hc : (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) ≤
      (1 - 2 * η * lam) * (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) +
        η ^ 2 * G ^ 2 := by nlinarith
  have hgap : 2 * η * (∫ S, (F (w t S) - F a) ∂iidLaw D (n + 1)) ≤
      (1 - η * lam) * (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) -
      (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) + η ^ 2 * G ^ 2 := by nlinarith
  constructor
  · dsimp [η, w] at hc
    convert hc using 1; field_simp
  · have htpos : (0 : ℝ) < t + 1 := by positivity
    change 2 * (∫ S, (F (w t S) - F a) ∂iidLaw D (n + 1)) ≤
      lam * t * (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) -
      lam * (t + 1) * (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) +
      G ^ 2 / (lam * (t + 1))
    apply (mul_le_mul_iff_right₀ hη).mp
    calc
      η * (2 * (∫ S, (F (w t S) - F a) ∂iidLaw D (n + 1))) =
          2 * η * (∫ S, (F (w t S) - F a) ∂iidLaw D (n + 1)) := by ring
      _ ≤ (1 - η * lam) * (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) -
          (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) + η ^ 2 * G ^ 2 := hgap
      _ = η * (lam * t * (∫ S, ‖w t S - a‖ ^ 2 ∂iidLaw D (n + 1)) -
          lam * (t + 1) * (∫ S, ‖w (t + 1) S - a‖ ^ 2 ∂iidLaw D (n + 1)) +
          G ^ 2 / (lam * (t + 1))) := by
        dsimp [η]
        field_simp
        ring

end SuffixSGDProof
-- END ExpectedStep

-- BEGIN NativeRoot
open MeasureTheory UnderstandingML Filter Topology
open scoped InnerProductSpace BigOperators ENNReal NNReal

namespace OptimalSGD.Suffix

/-- **Theorem 5** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, §5, p. 6; proof App. B.6,
p. 18). Consider projected SGD started at `w₁ = 0` with step sizes `η_t = 1/(λt)` on the closed
convex set `W ∋ 0`, an i.i.d. sample `S ∼ D^T`, and α-suffix averaging with `α ∈ (0, 1)` and
`k = (1 − α)T` an integer. Suppose `F` is `λ`-strongly convex on `W`, the oracle mean
`E_z g(w, z)` is a subgradient of `F` relative to `W` at every `w ∈ W`, `E‖g(w, z)‖² ≤ G²` at
every `w ∈ W`, and `w*` minimizes `F` over `W`. Then `F(w̄ᵅ_T)` has a finite expectation and
`E[F(w̄ᵅ_T) − F(w*)] ≤ (2 + 2.5 log(1/(1 − α)))/α · G²/(λT)`, `log` the natural logarithm. -/
theorem theorem_5
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T) (hk : (k : ℝ) = (1 - α) * T) :
    Integrable (fun S => F (suffixAverage lam W g S k)) (iidLaw D T) ∧
    ∫ S, (F (suffixAverage lam W g S k) - F wstar) ∂(iidLaw D T) ≤
      (2 + 2.5 * Real.log (1 / (1 - α))) / α * (G ^ 2 / (lam * T)) := by
  have : IsProbabilityMeasure (iidLaw D T) := by unfold iidLaw; infer_instance
  have hkpos : 0<k := by
    have : (0:ℝ)<k := by rw [hk]; positivity
    exact_mod_cast this
  have hkT : k<T := by
    have : (k:ℝ)<T := by rw [hk]; nlinarith [show (0:ℝ)<T by exact_mod_cast hT]
    exact_mod_cast this
  have hn : ((T-k:ℕ):ℝ)=α*T := by rw [Nat.cast_sub hkT.le, hk]; ring
  let w (t : ℕ) (S : Fin T→Z) := sgdStrongIterates lam W g S t
  let distE (t : ℕ) := ∫ S, ‖w t S-wstar‖^2 ∂iidLaw D T
  let gapE (t : ℕ) := ∫ S, (F (w t S)-F wstar) ∂iidLaw D T
  have hmem (t : ℕ) (S : Fin T→Z) : w t S∈W :=
    SuffixSGDProof.run_mem lam W g hW0 (SuffixSGDProof.proj_mem hWconv hWclosed hW0) S t
  have hlip (u : Vec d) (hu : u ∈ W) (v : Vec d) (hv : v ∈ W) :
      |F u - F v| ≤ |G| * ‖u-v‖ :=  SuffixSGDProof.objective_lipschitz D g horacle hmoment hu hv
  have hb (u : Vec d) (hu : u ∈ W) : ‖u-wstar‖ ≤ 2*|G|/lam :=  SuffixSGDProof.domain_bound hlam hF hwstar hmin hu (hlip u hu wstar hwstar)
  have hri := SuffixSGDProof.run_integrable W hWconv hWclosed hW0 F hlam hF D g hg horacle hmoment wstar hwstar hmin T
  have hdn (t : ℕ) : 0≤distE t := integral_nonneg fun _ => sq_nonneg _
  have hdz : distE 0≤4*(G^2/lam^2) := by
    have hd := hb 0 hW0
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*|G|/lam)).2 hd
    dsimp [distE,w,sgdStrongIterates]
    simp only [integral_const, probReal_univ, one_smul]
    have he : (2*|G|/lam)^2=4*(G^2/lam^2) := by
      rw [div_pow, mul_pow, sq_abs]
      ring
    rwa [he] at hsq
  have hrec := SuffixSGDProof.expected_recurrences W hWconv hWclosed hW0 F hlam hF D g hg horacle hmoment wstar hwstar hmin T
  have hdr := SuffixSGDProof.distance_rate (show 0≤G^2/lam^2 by positivity) distE T hdn hdz
    (fun t ht => by simpa only [distE,w,div_div] using (hrec t ht).1)
  have hdk : distE k≤4*G^2/(lam^2*((k:ℝ)+1)) := by
    calc
      distE k ≤ 4*(G^2/lam^2)/((k:ℝ)+1) := hdr k hkT.le
      _ = _ := by field_simp
  have hs := SuffixSGDProof.suffix_scalar hlam (sq_nonneg G) distE gapE k T hkpos hkT hdn hdk
    (fun t ht => (hrec t (Finset.mem_Ico.mp ht).2).2)
  have hconv : ConvexOn ℝ W F := strongConvexOn_zero.mp (hF.mono hlam.le)
  have hamem (S : Fin T→Z) : suffixAverage lam W g S k∈W :=
    SuffixSGDProof.average_mem hWconv (fun t => w t S) k T hkT (fun t _ => hmem t S)
  have hai := SuffixSGDProof.bounded_objective_integrable (iidLaw D T)
    hWconv hWclosed hW0 hwstar hlip hb (fun S : Fin T→Z => suffixAverage lam W g S k)
    (SuffixSGDProof.measurable_suffix lam W g (SuffixSGDProof.continuous_proj hWconv hWclosed hW0) hg T k) hamem
  refine ⟨hai.1, ?_⟩
  have hj := SuffixSGDProof.integral_average_gap (iidLaw D T) F w wstar k T hkT hai.1
    (fun t _ => (hri t).1)
    (fun S => SuffixSGDProof.average_jensen hconv (fun t => w t S) k T hkT (fun t _ => hmem t S))
  change (∫ S, (F (suffixAverage lam W g S k)-F wstar) ∂iidLaw D T)≤
    ((T-k:ℕ):ℝ)⁻¹*(∑ t∈Finset.Ico k T,gapE t) at hj
  have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0≤((T-k:ℕ):ℝ)⁻¹)
  have htp : (0:ℝ)<T := by exact_mod_cast hT
  have hkp : (0:ℝ)<k := by exact_mod_cast hkpos
  have hlog : Real.log T-Real.log k=Real.log (1/(1-α)) := by
    rw [←Real.log_div (ne_of_gt htp) (ne_of_gt hkp), hk]
    congr 1
    field_simp
  rw [hlog,hn] at hs'
  have hln : 0≤Real.log (1/(1-α)) := by
    apply Real.log_nonneg
    rw [one_le_div (by linarith)]
    linarith
  have hwk : (α*T)⁻¹*(G^2/lam*(2+Real.log (1/(1-α))/2))≤
      (2+2.5*Real.log (1/(1-α)))/α*(G^2/(lam*T)) := by
    field_simp
    nlinarith [mul_nonneg (sq_nonneg G) hln]
  rw [hn] at hj
  exact hj.trans (hs'.trans hwk)

end OptimalSGD.Suffix
-- END NativeRoot

open OptimalSGD.Suffix MeasureTheory UnderstandingML

theorem solution
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T) (hk : (k : ℝ) = (1 - α) * T) :
    Integrable (fun S => F (suffixAverage lam W g S k)) (iidLaw D T) ∧
    ∫ S, (F (suffixAverage lam W g S k) - F wstar) ∂(iidLaw D T) ≤
      (2 + 2.5 * Real.log (1 / (1 - α))) / α * (G ^ 2 / (lam * T)) :=
  OptimalSGD.Suffix.theorem_5 W hWconv hWclosed hW0 F hlam hF D g hg horacle hmoment wstar hwstar hmin hα0 hα1 T k hT hk
