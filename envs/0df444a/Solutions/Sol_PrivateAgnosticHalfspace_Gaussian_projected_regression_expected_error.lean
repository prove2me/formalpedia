-- Prove2me | solution 1 for PrivateAgnosticHalfspace.Gaussian.projected_regression_expected_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:15:03.18217+00:00
-- url     : https://prove2.me/submissions/3148401a-8ae7-4b89-b936-4954a2fd8aa0

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
import Definitions.Def_NonconvexAG_StochComposite_RSAG
import Mathlib.Algebra.BigOperators.Intervals
import Theorems.Thm_FunctionalInequalities_Analysis_exists_subgradient_slope_le_inner_add_readable
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Definitions.Def_NonconvexAG_StochComposite_ProxMap
import Theorems.Thm_NonconvexAG_StochComposite_eq_summed
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_lemma_B_8

section
-- Solutions.AcceleratedRegressionSchedule
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def accelAlpha (k : ℕ) : ℝ := 2/((k : ℝ)+1)
noncomputable def accelLambda (β : ℝ) (k : ℕ) : ℝ := (k : ℝ)*β/2
lemma accelGamma_succ (k : ℕ) :
    NonconvexAG.Smooth.Gamma accelAlpha (k+1) = 2/(((k : ℝ)+1)*((k : ℝ)+2)) := by
  induction k with
  | zero => norm_num [NonconvexAG.Smooth.Gamma,accelAlpha]
  | succ k ih =>
    have he : NonconvexAG.Smooth.Gamma accelAlpha (k+2) =
        NonconvexAG.Smooth.Gamma accelAlpha (k+1)*(1-accelAlpha (k+2)) := by
      exact prod_Icc_succ_top (by omega) _
    rw [show k+1+1 = k+2 by omega,he,ih]
    unfold accelAlpha
    push_cast
    field_simp
    ring
lemma accelGamma_formula (k : ℕ) (hk : 1 ≤ k) :
    NonconvexAG.Smooth.Gamma accelAlpha k = 2/((k : ℝ)*((k : ℝ)+1)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  convert! accelGamma_succ j using 1 <;> push_cast <;> ring
lemma accelGamma_pos (k : ℕ) (hk : 1 ≤ k) : 0 < NonconvexAG.Smooth.Gamma accelAlpha k := by
  rw [accelGamma_formula k hk]
  apply div_pos (by norm_num)
  have h : (0 : ℝ) < k := by exact_mod_cast hk
  positivity
lemma accel_steps (β : ℝ) (hβ : 0 < β) :
    NonconvexAG.StochComposite.RSAGStepsizes accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) := by
  refine ⟨by norm_num [accelAlpha],?_,fun _ _ => hβ,?_,fun _ _ => le_rfl⟩
  · intro k hk
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    unfold accelAlpha
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  · intro k hk
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    unfold accelLambda
    positivity
lemma accel_ratio (β : ℝ) (hβ : 0 < β) (k : ℕ) (hk : 1 ≤ k) :
    accelAlpha k / (accelLambda β k*NonconvexAG.Smooth.Gamma accelAlpha k) = 2/β := by
  rw [accelGamma_formula k hk]
  unfold accelAlpha accelLambda
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp <;> ring
lemma accel_step_conditions (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 < β) (hLβ : L*β ≤ 1/2)
    (N : ℕ) :
    (∀ k ∈ Icc 1 N, accelAlpha k*accelLambda β k ≤ β ∧ L*β < 1) ∧
    (∀ k ∈ Icc 1 N, 2 ≤ k →
      accelAlpha k/(accelLambda β k*NonconvexAG.Smooth.Gamma accelAlpha k) ≤
      accelAlpha (k-1)/(accelLambda β (k-1)*NonconvexAG.Smooth.Gamma accelAlpha (k-1))) := by
  constructor
  · intro k hk
    refine ⟨?_,by linarith⟩
    unfold accelAlpha accelLambda
    have hkR : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
    have he : 2/((k : ℝ)+1)*((k : ℝ)*β/2) = β*(k : ℝ)/((k : ℝ)+1) := by ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  · intro k hk hk2
    rw [accel_ratio β hβ k (by omega),accel_ratio β hβ (k-1) (by omega)]
lemma accelGamma_inv_mono (k N : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (NonconvexAG.Smooth.Gamma accelAlpha k)⁻¹ ≤ (NonconvexAG.Smooth.Gamma accelAlpha N)⁻¹ := by
  rw [accelGamma_formula k hk, accelGamma_formula N (hk.trans hkN)]
  rw [inv_div,inv_div]
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hknR : (k : ℝ) ≤ N := by exact_mod_cast hkN
  nlinarith
lemma accel_variance_weight_bound (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 < β)
    (hLβ : L*β ≤ 1/2) (k : ℕ) (hk : 1 ≤ k) :
    β*(4+(1-L*β)^2)/(4*NonconvexAG.Smooth.Gamma accelAlpha k*(1-L*β)) ≤
      3*β*(NonconvexAG.Smooth.Gamma accelAlpha k)⁻¹ := by
  have hG := accelGamma_pos k hk
  have hs : 1/2 ≤ 1-L*β := by linarith
  have hs1 : 1-L*β ≤ 1 := by nlinarith
  apply (div_le_iff₀ (by positivity : 0 < 4*NonconvexAG.Smooth.Gamma accelAlpha k*(1-L*β))).mpr
  have he : 3*β*(NonconvexAG.Smooth.Gamma accelAlpha k)⁻¹*
      (4*NonconvexAG.Smooth.Gamma accelAlpha k*(1-L*β)) = 12*β*(1-L*β) := by
    field_simp
    ring
  rw [he]
  have hsq : (1-L*β)^2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hβ.le (show 0 ≤ 12*(1-L*β)-(4+(1-L*β)^2) by linarith)]
lemma accel_variance_sum_bound (L β : ℝ) (hL : 0 ≤ L) (hβ : 0 < β)
    (hLβ : L*β ≤ 1/2) (N : ℕ) (hN : 1 ≤ N) :
    NonconvexAG.Smooth.Gamma accelAlpha N *
      (∑ k ∈ Icc 1 N, β*(4+(1-L*β)^2)/(4*NonconvexAG.Smooth.Gamma accelAlpha k*(1-L*β))) ≤
        3*β*N := by
  have hG := accelGamma_pos N hN
  calc
    _ ≤ NonconvexAG.Smooth.Gamma accelAlpha N *
        ∑ _k ∈ Icc 1 N, 3*β*(NonconvexAG.Smooth.Gamma accelAlpha N)⁻¹ := by
      gcongr with k hk
      exact (accel_variance_weight_bound L β hL hβ hLβ k (mem_Icc.mp hk).1).trans
        (mul_le_mul_of_nonneg_left (accelGamma_inv_mono k N (mem_Icc.mp hk).1 (mem_Icc.mp hk).2) (by positivity))
    _ = _ := by
      simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id,nsmul_eq_mul]
      field_simp <;> ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AcceleratedPath
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
lemma batchEnd_one (k : ℕ) : batchEnd (fun _ => 1) k = k := by
  simp [batchEnd,Nat.card_Icc]
lemma sampleAvg_one {D : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (k : ℕ) (hk : 1 ≤ k) (v : Vec D) (s : ℕ → Ξ) :
    sampleAvg G (fun _ => 1) k v s = G v (s k) := by
  simp [sampleAvg,batchEnd_one,Nat.sub_add_cancel hk]
lemma rsagPath_one_congr {D : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D)
    (s t : ℕ → Ξ) (k : ℕ) (hst : ∀ j, 1 ≤ j → j ≤ k → s j = t j) :
    rsagPath G P α β lam (fun _ => 1) x0 s k = rsagPath G P α β lam (fun _ => 1) x0 t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp := ih (fun j hj hjk => hst j hj (by omega))
    simp only [rsagPath,hp,sampleAvg_one G (k+1) (by omega),hst (k+1) (by omega) le_rfl]
noncomputable def finiteNoiseSequence {Ξ : Type*} {N : ℕ} (z0 : Ξ)
    (s : Fin (N+1) → Ξ) (k : ℕ) : Ξ := if hk : k < N+1 then s ⟨k,hk⟩ else z0
lemma finiteNoiseSequence_apply {Ξ : Type*} {N : ℕ} (z0 : Ξ) (s : Fin (N+1) → Ξ)
    (k : ℕ) (hk : k ≤ N) : finiteNoiseSequence z0 s k = s ⟨k,by omega⟩ := by
  simp [finiteNoiseSequence,show k < N+1 by omega]
lemma finiteNoiseSequence_measurable {Ξ : Type*} [MeasurableSpace Ξ] {N : ℕ}
    (z0 : Ξ) (k : ℕ) : Measurable (fun s : Fin (N+1) → Ξ => finiteNoiseSequence z0 s k) := by
  unfold finiteNoiseSequence
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const
lemma rsagPath_one_measurable {D : ℕ} {Ξ W : Type*} [MeasurableSpace Ξ] [MeasurableSpace W]
    (G : Vec D → Ξ → Vec D) (hG : Measurable (Function.uncurry G))
    (P : Vec D → Vec D → ℝ → Vec D) (hP : Measurable (fun q : (Vec D × Vec D) × ℝ => P q.1.1 q.1.2 q.2))
    (α β lam : ℕ → ℝ) (x0 : Vec D) (ξ : ℕ → W → Ξ) (hξ : ∀ k, Measurable (ξ k)) (k : ℕ) :
    Measurable (fun ω => rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have hmd : Measurable (fun ω => (1-α (k+1)) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).2 + α (k+1) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).1) :=
      by convert! (ih.snd.const_smul (1-α (k+1))).add (ih.fst.const_smul (α (k+1))) using 1
    have hg : Measurable (fun ω => G ((1-α (k+1)) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).2 + α (k+1) •
        (rsagPath G P α β lam (fun _ => 1) x0 (fun j => ξ j ω) k).1) (ξ (k+1) ω)) :=
      by convert! hG.comp (hmd.prodMk (hξ (k+1))) using 1
    simp only [rsagPath,sampleAvg_one G (k+1) (by omega)]
    convert! (hP.comp ((ih.fst.prodMk hg).prodMk measurable_const)).prodMk
      (hP.comp ((hmd.prodMk hg).prodMk measurable_const)) using 1
lemma rsagPath_finite_update {D N : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D) (z0 z : Ξ)
    (s : Fin (N+1) → Ξ) (i : Fin (N+1)) (k : ℕ) (hki : k < i.val) :
    rsagPath G P α β lam (fun _ => 1) x0 (finiteNoiseSequence z0 (Function.update s i z)) k =
      rsagPath G P α β lam (fun _ => 1) x0 (finiteNoiseSequence z0 s) k := by
  apply rsagPath_one_congr
  intro j hj hjk
  rw [finiteNoiseSequence_apply _ _ j (by omega),finiteNoiseSequence_apply _ _ j (by omega)]
  apply Function.update_of_ne
  intro he
  have : j = i.val := congrArg Fin.val he
  omega
lemma rsagPath_projected_mem {D : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (Ω : Set (Vec D)) (π : Vec D → Vec D) (hπ : ∀ x, π x ∈ Ω)
    (α β lam : ℕ → ℝ) (x0 : Vec D) (hx0 : x0 ∈ Ω) (s : ℕ → Ξ) (k : ℕ) :
    (rsagPath G (fun x y c => π (x-c • y)) α β lam (fun _ => 1) x0 s k).1 ∈ Ω ∧
      (rsagPath G (fun x y c => π (x-c • y)) α β lam (fun _ => 1) x0 s k).2 ∈ Ω := by
  cases k with
  | zero => exact ⟨hx0,hx0⟩
  | succ k => exact ⟨hπ _,hπ _⟩
lemma deltaBar_one {D : ℕ} {Ξ W : Type*} (G : Vec D → Ξ → Vec D) (g : Vec D → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D)
    (ξ : ℕ → W → Ξ) (k : ℕ) (hk : 1 ≤ k) (ω : W) :
    deltaBar G g P α β lam (fun _ => 1) x0 ξ k ω =
      G (xmdSeq G P α β lam (fun _ => 1) x0 ξ k ω) (ξ k ω)-
        g (xmdSeq G P α β lam (fun _ => 1) x0 ξ k ω) := by
  simp only [deltaBar,Gbar,sampleAvg_one G k hk]
lemma xmdSeq_finite_update {D N : ℕ} {Ξ : Type*} (G : Vec D → Ξ → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D) (z0 z : Ξ)
    (s : Fin (N+1) → Ξ) (i : Fin (N+1)) (hi : 1 ≤ i.val) :
    xmdSeq G P α β lam (fun _ => 1) x0 (fun k s => finiteNoiseSequence z0 s k) i.val (Function.update s i z) =
      xmdSeq G P α β lam (fun _ => 1) x0 (fun k s => finiteNoiseSequence z0 s k) i.val s := by
  have h := rsagPath_finite_update G P α β lam x0 z0 z s i (i.val-1) (by omega)
  simp only [xmdSeq,xagSeq,xSeq]
  rw [h]
lemma rsagPath_one_parameter {D : ℕ} {Z Ξ : Type*} (G : Z → Vec D → Ξ → Vec D)
    (P : Vec D → Vec D → ℝ → Vec D) (α β lam : ℕ → ℝ) (x0 : Vec D)
    (z : Z) (s : ℕ → Ξ) (k : ℕ) :
    rsagPath (fun (v : Vec D) (q : Z × Ξ) => G q.1 v q.2) P α β lam (fun _ => 1) x0 (fun j => (z,s j)) k =
      rsagPath (G z) P α β lam (fun _ => 1) x0 s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rsagPath,ih,sampleAvg_one _ (k+1) (by omega)]
end PrivateAgnosticHalfspace.Gaussian


end

section
-- Solutions.ConvexERMGeometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma subgradient_norm_le_lipschitz {D : ℕ} (f : Vec D → ℝ) (T : ℝ≥0)
    (hf : LipschitzWith T f) (x g : Vec D)
    (hg : ∀ y, f x + inner ℝ g (y-x) ≤ f y) : ‖g‖ ≤ T := by
  have hsub := hg (x+g)
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hsub
  have hlip := hf.norm_sub_le (x+g) x
  simp only [add_sub_cancel_left] at hlip
  have habs := le_abs_self (f (x+g)-f x)
  rw [← Real.norm_eq_abs] at habs
  nlinarith [norm_nonneg g]
lemma exists_bounded_subgradient_oracle {Z : Type*} (D : ℕ) (ℓ : Vec D → Z → ℝ)
    (T : ℝ≥0) (hc : ∀ z, ConvexOn ℝ univ (fun v => ℓ v z))
    (hl : ∀ z, LipschitzWith T (fun v => ℓ v z)) :
    ∃ g : Z → Vec D → Vec D, IsSubgradient D ℓ g ∧ ∀ z v, ‖g z v‖ ≤ T := by
  have he (z : Z) (v : Vec D) : ∃ g, ∀ w, ℓ v z + inner ℝ g (w-v) ≤ ℓ w z := by
    obtain ⟨g,hg,_⟩ := FunctionalInequalities.Analysis.exists_subgradient_slope_le_inner_add_readable
      (hc z) v 0
    exact ⟨g,hg⟩
  choose g hg using he
  exact ⟨g,hg,fun z v => subgradient_norm_le_lipschitz _ T (hl z) v (g z v) (hg z v)⟩
lemma exists_projection_oracle (D : ℕ) (Ω : Set (Vec D)) (hne : Ω.Nonempty)
    (hcompact : IsCompact Ω) : ∃ π : Vec D → Vec D, IsProjection D Ω π := by
  have he (v : Vec D) : ∃ p ∈ Ω, ∀ w ∈ Ω, ‖p-v‖ ≤ ‖w-v‖ := by
    obtain ⟨p,hp,hmin⟩ := hcompact.exists_isMinOn hne (by fun_prop : ContinuousOn (fun p => ‖p-v‖) Ω)
    exact ⟨p,hp,hmin⟩
  choose π hπ hmin using he
  exact ⟨π,fun v => ⟨hπ v,hmin v⟩⟩
lemma empirical_minimum_attained {Z : Type*} (D n : ℕ) (ℓ : Vec D → Z → ℝ)
    (S : Fin n → Z) (Ω : Set (Vec D)) (hne : Ω.Nonempty) (hcompact : IsCompact Ω)
    (hc : ∀ z, Continuous (fun v => ℓ v z)) :
    ∃ v ∈ Ω, generalEmpiricalLoss D ℓ S v = empiricalMinimum D ℓ S Ω := by
  have hcont : Continuous (generalEmpiricalLoss D ℓ S) := by
    unfold generalEmpiricalLoss
    exact (continuous_finset_sum _ (fun i _ => hc (S i))).div_const _
  obtain ⟨v,hv,hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  refine ⟨v,hv,?_⟩
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨v,hv,rfl⟩,?_⟩
  rintro y ⟨w,hw,rfl⟩
  exact hmin hw
lemma projection_variational {D : ℕ} (Ω : Set (Vec D)) (hc : Convex ℝ Ω)
    (π : Vec D → Vec D) (hπ : IsProjection D Ω π) (x w : Vec D) (hw : w ∈ Ω) :
    inner ℝ (x-π x) (w-π x) ≤ 0 := by
  letI : Nonempty Ω := ⟨⟨π x,(hπ x).1⟩⟩
  apply (norm_eq_iInf_iff_real_inner_le_zero hc (hπ x).1).mp ?_ w hw
  apply le_antisymm
  · apply le_ciInf
    intro y
    calc
      ‖x-π x‖ = ‖π x-x‖ := norm_sub_rev _ _
      _ ≤ ‖y.val-x‖ := (hπ x).2 y y.property
      _ = ‖x-y.val‖ := norm_sub_rev _ _
  · have hbb : BddBelow (Set.range (fun y : Ω => ‖x-y.val‖)) := by
      refine ⟨0,?_⟩
      rintro _ ⟨y,rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbb (⟨π x,(hπ x).1⟩ : Ω)
lemma projection_nonexpansive {D : ℕ} (Ω : Set (Vec D)) (hc : Convex ℝ Ω)
    (π : Vec D → Vec D) (hπ : IsProjection D Ω π) : LipschitzWith 1 π := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h1 := projection_variational Ω hc π hπ x (π y) (hπ y).1
  have h2 := projection_variational Ω hc π hπ y (π x) (hπ x).1
  have he : inner ℝ (x-y) (π x-π y) = ‖π x-π y‖^2 -
      inner ℝ (x-π x) (π y-π x) - inner ℝ (y-π y) (π x-π y) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hbound := real_inner_le_norm (x-y) (π x-π y)
  nlinarith [norm_nonneg (π x-π y), norm_nonneg (x-y)]
lemma projection_fixes {D : ℕ} (Ω : Set (Vec D)) (π : Vec D → Vec D)
    (hπ : IsProjection D Ω π) (x : Vec D) (hx : x ∈ Ω) : π x = x := by
  have h := (hπ x).2 x hx
  simp only [sub_self, norm_zero, norm_le_zero_iff] at h
  exact sub_eq_zero.mp h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ProjectedProxMap
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma shifted_norm_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z x y : E) (c : ℝ) :
    ‖z-(x-c • y)‖^2 = ‖z-x‖^2+2*c*inner ℝ y z-2*c*inner ℝ y x+c^2*‖y‖^2 := by
  simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,conj_trivial]
  simp only [real_inner_comm]
  ring
lemma projection_as_prox {D : ℕ} (Ω : Set (Vec D)) (π : Vec D → Vec D)
    (hπ : IsProjection D Ω π) :
    NonconvexAG.StochComposite.IsProxMap Ω (fun _ => 0) (fun x y c => π (x-c • y)) := by
  intro x y c hc
  refine ⟨(hπ (x-c • y)).1,?_⟩
  intro u hu
  have hdist := (hπ (x-c • y)).2 u hu
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hdist
  rw [shifted_norm_square,shifted_norm_square] at hs
  simp only [add_zero]
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<2*c)).mp
  have he (z : Vec D) : (2*c)*(inner ℝ y z+‖z-x‖^2/(2*c)) =
      2*c*inner ℝ y z+‖z-x‖^2 := by field_simp [hc.ne'] <;> ring
  rw [he,he]
  linarith
lemma projection_as_prox_bounded {D : ℕ} (Ω : Set (Vec D)) (π : Vec D → Vec D)
    (hπ : IsProjection D Ω π) (M : ℝ) (hM : ∀ x ∈ Ω, ‖x‖ ≤ M) :
    NonconvexAG.StochComposite.Assumption2 (fun x y c => π (x-c • y)) M := by
  intro x y c hc
  exact hM _ (hπ _).1
lemma projection_as_prox_measurable {D : ℕ} (Ω : Set (Vec D)) (hc : Convex ℝ Ω)
    (π : Vec D → Vec D) (hπ : IsProjection D Ω π) :
    Measurable (fun z : Vec D × Vec D × ℝ => π (z.1-z.2.2 • z.2.1)) := by
  apply (projection_nonexpansive Ω hc π hπ).continuous.measurable.comp
  fun_prop
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.AcceleratedFiniteUtility
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
lemma accelerated_projected_finite_utility {D : ℕ}
    (F : Vec D → ℝ) (g : Vec D → Vec D) (L : ℝ)
    (hsmooth : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hconv : ConvexOn ℝ univ F)
    (Ω : Set (Vec D)) (hΩ : Convex ℝ Ω) (π : Vec D → Vec D) (hπ : IsProjection D Ω π)
    {Ξ W : Type*} [MeasurableSpace W]
    (G : Vec D → Ξ → Vec D) (μ : Measure W) [IsProbabilityMeasure μ] (ξ : ℕ → W → Ξ)
    (σ β : ℝ) (hβ : 0 < β) (hLβ : L*β ≤ 1/2) (x0 : Vec D)
    (N : ℕ) (hN : 1 ≤ N) (xstar : Vec D) (hxstar : xstar ∈ Ω)
    (hgap : Integrable (fun ω => F (xagSeq G (fun x y c => π (x-c • y)) accelAlpha
      (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ N ω)-F xstar) μ)
    (hcross : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => inner ℝ (deltaBar G g (fun x y c => π (x-c • y)) accelAlpha
        (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ k ω)
        (xstar-xSeq G (fun x y c => π (x-c • y)) accelAlpha
          (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ (k-1) ω)) μ ∧
      (∫ ω, inner ℝ (deltaBar G g (fun x y c => π (x-c • y)) accelAlpha
        (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ k ω)
        (xstar-xSeq G (fun x y c => π (x-c • y)) accelAlpha
          (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ (k-1) ω) ∂μ) = 0)
    (hvar : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => ‖deltaBar G g (fun x y c => π (x-c • y)) accelAlpha
        (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ k ω‖^2) μ ∧
      (∫ ω, ‖deltaBar G g (fun x y c => π (x-c • y)) accelAlpha
        (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ k ω‖^2 ∂μ) ≤ σ^2) :
    (∫ ω, F (xagSeq G (fun x y c => π (x-c • y)) accelAlpha
      (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ N ω)-F xstar ∂μ) ≤
      NonconvexAG.Smooth.Gamma accelAlpha N * (‖x0-xstar‖^2/β) + 3*σ^2*β*N := by
  let P := fun (x y : Vec D) (c : ℝ) => π (x-c • y)
  let ag := xagSeq G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ
  let x := xSeq G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ
  let md := xmdSeq G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ
  let err := deltaBar G g P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) x0 ξ
  let Γ := NonconvexAG.Smooth.Gamma accelAlpha
  let cross := fun k ω => inner ℝ (err k ω) (xstar-x (k-1) ω)
  let variance := fun k ω => ‖err k ω‖^2
  let a := fun k => accelAlpha k/Γ k
  let b := fun k => β/(Γ k*(1-L*β))
  have hΓ (k : ℕ) (hk : 1 ≤ k) : 0 < Γ k := accelGamma_pos k hk
  have hb (k : ℕ) (hk : k ∈ Finset.Icc 1 N) : 0 ≤ b k := by
    apply div_nonneg hβ.le
    apply mul_nonneg (hΓ k (mem_Icc.mp hk).1).le
    linarith
  have hz : ConvexOptAlg.SmoothGD.IsBetaSmooth (fun _ : Vec D => 0) (fun _ => 0) 0 := by
    refine ⟨le_rfl,fun z => hasGradientAt_const z 0,?_⟩
    intro z w
    simp
  have hX : ConvexOn ℝ Ω (fun _ : Vec D => (0 : ℝ)) := ⟨hΩ,by intros; simp⟩
  have hc := accel_step_conditions L β hsmooth.1 hβ hLβ N
  have hs := NonconvexAG.StochComposite.eq_summed
    (fun _ : Vec D => 0) F (fun _ => 0) g 0 L hz hsmooth hconv
    F g L (by funext z; simp) (by funext z; simp) (by simp)
    Ω (fun _ => 0) hX P (projection_as_prox Ω π hπ) G
    accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) (accel_steps β hβ) x0 ξ N hN hc.1 hc.2
  have hinit : 2*accelLambda β 1 = β := by norm_num [accelLambda]; ring
  have hpoint (ω : W) : (F (ag N ω)-F xstar)/Γ N ≤
      ‖x0-xstar‖^2/β + ∑ k ∈ Finset.Icc 1 N, a k*cross k ω + ∑ k ∈ Finset.Icc 1 N, b k*variance k ω := by
    have h := hs ω xstar hxstar
    simp only [zero_div,zero_mul,add_zero,zero_add,hinit] at h
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 N, (1-L*β)/(4*β*Γ k)*‖ag k ω-md k ω‖^2 := by
      apply sum_nonneg
      intro k hk
      apply mul_nonneg _ (sq_nonneg _)
      exact div_nonneg (by linarith) (by positivity [hΓ k (mem_Icc.mp hk).1])
    have hd := (le_add_of_nonneg_right hnonneg).trans h
    convert! hd using 1 <;> simp only [a,b,cross,variance,P,ag,x,md,err,Γ,div_mul_eq_mul_div]
  have hir : Integrable (fun ω => ‖x0-xstar‖^2/β + ∑ k ∈ Finset.Icc 1 N, a k*cross k ω +
      ∑ k ∈ Finset.Icc 1 N, b k*variance k ω) μ :=
    ((integrable_const _).add (integrable_finsetSum _ (fun k hk => (hcross k hk).1.const_mul (a k)))).add
      (integrable_finsetSum _ (fun k hk => (hvar k hk).1.const_mul (b k)))
  have h := integral_mono (hgap.div_const (Γ N)) hir hpoint
  have hri : (∫ ω, ‖x0-xstar‖^2/β + ∑ k ∈ Finset.Icc 1 N, a k*cross k ω +
      ∑ k ∈ Finset.Icc 1 N, b k*variance k ω ∂μ) =
      ‖x0-xstar‖^2/β + ∑ k ∈ Finset.Icc 1 N, b k*(∫ ω, variance k ω ∂μ) := by
    rw [integral_add (f := fun ω => ‖x0-xstar‖^2/β + ∑ k ∈ Finset.Icc 1 N, a k*cross k ω)
      (g := fun ω => ∑ k ∈ Finset.Icc 1 N, b k*variance k ω) ((integrable_const _).add (integrable_finsetSum _
      (fun k hk => (hcross k hk).1.const_mul (a k))))
      (integrable_finsetSum _ (fun k hk => (hvar k hk).1.const_mul (b k))),
      integral_add (f := fun _ : W => ‖x0-xstar‖^2/β)
        (g := fun ω => ∑ k ∈ Finset.Icc 1 N, a k*cross k ω) (integrable_const _) (integrable_finsetSum _ (fun k hk => (hcross k hk).1.const_mul (a k))),
      integral_finsetSum _ (fun k hk => (hcross k hk).1.const_mul (a k)),
      integral_finsetSum _ (fun k hk => (hvar k hk).1.const_mul (b k))]
    simp only [integral_const,probReal_univ,one_smul,integral_const_mul]
    have hzero : ∑ k ∈ Finset.Icc 1 N, a k*(∫ ω, cross k ω ∂μ) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [(hcross k hk).2,mul_zero]
    rw [hzero,add_zero]
  rw [hri,integral_div] at h
  have hv : ∑ k ∈ Finset.Icc 1 N, b k*(∫ ω, variance k ω ∂μ) ≤ σ^2 * ∑ k ∈ Finset.Icc 1 N,
      β*(4+(1-L*β)^2)/(4*Γ k*(1-L*β)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro k hk
    calc
      _ ≤ b k*σ^2 := mul_le_mul_of_nonneg_left (hvar k hk).2 (hb k hk)
      _ ≤ _ := by
        rw [mul_comm (σ^2)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp [b]
        have hden : 0 < Γ k*(1-L*β) := mul_pos (hΓ k (mem_Icc.mp hk).1) (by linarith)
        have hden4 : 0 < 4*Γ k*(1-L*β) := by nlinarith [hden]
        apply (div_le_div_iff₀ hden hden4).mpr
        nlinarith [mul_nonneg hβ.le (mul_nonneg (sq_nonneg (1-L*β)) hden.le)]
  have ht := accel_variance_sum_bound L β hsmooth.1 hβ hLβ N hN
  have hscaled := (div_le_iff₀ (hΓ N hN)).mp (h.trans (add_le_add_right hv _))
  nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.mpr ht)]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteNoiseIntegration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma finite_coordinate_integral {Ξ E : Type*} [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {N : ℕ} (μ : Fin (N+1) → Measure Ξ) [∀ i, IsProbabilityMeasure (μ i)]
    (i : Fin (N+1)) (f : (Fin (N+1) → Ξ) → E) (hf : Integrable f (Measure.pi μ)) :
    (∫ s, f s ∂Measure.pi μ) =
      ∫ t, ∫ z, f (i.insertNth z t) ∂μ i ∂Measure.pi (fun j => μ (i.succAbove j)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => Ξ) i
  have hp := (measurePreserving_piFinSuccAbove μ i).symm
  have hfi := hp.integrable_comp_of_integrable hf
  calc
    _ = ∫ q : Ξ × (Fin N → Ξ), f (e.symm q)
        ∂(μ i).prod (Measure.pi (fun j => μ (i.succAbove j))) := by
      exact (hp.integral_comp' f).symm
    _ = _ := by
      convert! integral_prod_symm _ hfi using 1
lemma finite_coordinate_centered_inner {Ξ : Type*} [MeasurableSpace Ξ] {D N : ℕ}
    (μ : Fin (N+1) → Measure Ξ) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (N+1))
    (a b : (Fin (N+1) → Ξ) → Vec D) (G : Vec D → Ξ → Vec D) (g : Vec D → Vec D)
    (z0 : Ξ) (ha : ∀ s z, a (Function.update s i z) = a s)
    (hb : ∀ s z, b (Function.update s i z) = b s)
    (hG : ∀ x, Integrable (G x) (μ i)) (hmean : ∀ x, (∫ z, G x z ∂μ i) = g x)
    (hf : Integrable (fun s => inner ℝ (G (a s) (s i)-g (a s)) (b s)) (Measure.pi μ)) :
    (∫ s, inner ℝ (G (a s) (s i)-g (a s)) (b s) ∂Measure.pi μ) = 0 := by
  rw [finite_coordinate_integral μ i _ hf]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro t
  have hap (z : Ξ) : a (i.insertNth z t) = a (i.insertNth z0 t) := by
    have h := ha (i.insertNth z0 t) z
    simpa only [Fin.update_insertNth] using h
  have hbp (z : Ξ) : b (i.insertNth z t) = b (i.insertNth z0 t) := by
    have h := hb (i.insertNth z0 t) z
    simpa only [Fin.update_insertNth] using h
  simp_rw [hap,hbp,Fin.insertNth_apply_same]
  simp_rw [real_inner_comm]
  have hi : Integrable (fun z => G (a (i.insertNth z0 t)) z - g (a (i.insertNth z0 t))) (μ i) := by
    convert! (hG (a (i.insertNth z0 t))).sub (integrable_const (g (a (i.insertNth z0 t)))) using 1
  rw [integral_inner hi _,
    integral_sub (hG _) (integrable_const _),hmean,integral_const]
  simp
lemma finite_coordinate_expectation_le {Ξ A : Type*} [MeasurableSpace Ξ] {N : ℕ}
    (μ : Fin (N+1) → Measure Ξ) [∀ i, IsProbabilityMeasure (μ i)] (i : Fin (N+1))
    (a : (Fin (N+1) → Ξ) → A) (F : A → Ξ → ℝ) (z0 : Ξ)
    (ha : ∀ s z, a (Function.update s i z) = a s) (V : ℝ)
    (hbound : ∀ x, (∫ z, F x z ∂μ i) ≤ V)
    (hf : Integrable (fun s => F (a s) (s i)) (Measure.pi μ)) :
    (∫ s, F (a s) (s i) ∂Measure.pi μ) ≤ V := by
  have hp := (measurePreserving_piFinSuccAbove μ i).symm
  have hi := (hp.integrable_comp_of_integrable hf).integral_prod_right
  rw [finite_coordinate_integral μ i _ hf]
  calc
    _ ≤ ∫ _ : Fin N → Ξ, V ∂Measure.pi (fun j => μ (i.succAbove j)) := by
      refine integral_mono ?_ (integrable_const _) ?_
      · convert! hi using 1
      · intro t
        have hap (z : Ξ) : a (i.insertNth z t) = a (i.insertNth z0 t) := by
          have h := ha (i.insertNth z0 t) z
          simpa only [Fin.update_insertNth] using h
        simp_rw [hap,Fin.insertNth_apply_same]
        exact hbound _
    _ = V := by simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteOracleMoments
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma finite_oracle_error_memLp {Ξ : Type*} [MeasurableSpace Ξ] {D N : ℕ}
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (G : Vec D → Ξ → Vec D) (g : Vec D → Vec D)
    (hG : Measurable (Function.uncurry G)) (hg : Measurable g)
    (R : Ξ → ℝ) (hR : MemLp R 2 μ) (hbound : ∀ x z, ‖G x z‖ ≤ R z)
    (T : ℝ) (hgBound : ∀ x, ‖g x‖ ≤ T)
    (a : (Fin (N+1) → Ξ) → Vec D) (ha : Measurable a) (i : Fin (N+1)) :
    MemLp (fun s => G (a s) (s i)-g (a s)) 2 (Measure.pi (fun _ : Fin (N+1) => μ)) := by
  have hGi : Measurable (fun s : Fin (N+1) → Ξ => G (a s) (s i)) := by
    convert! hG.comp (ha.prodMk (measurable_pi_apply i)) using 1
  have hgm : Measurable (fun s => g (a s)) := hg.comp ha
  have hGmem := (hR.comp_measurePreserving (measurePreserving_eval (fun _ : Fin (N+1) => μ) i)).mono'
    hGi.aestronglyMeasurable (ae_of_all _ (fun s => hbound (a s) (s i)))
  have hgmem : MemLp (fun s => g (a s)) 2 (Measure.pi (fun _ : Fin (N+1) => μ)) :=
    MemLp.of_bound hgm.aestronglyMeasurable T (ae_of_all _ (fun s => hgBound (a s)))
  convert! hGmem.sub hgmem using 1
lemma finite_oracle_cross_moment {Ξ : Type*} [MeasurableSpace Ξ] {D N : ℕ}
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (G : Vec D → Ξ → Vec D) (g : Vec D → Vec D)
    (hG : Measurable (Function.uncurry G)) (hg : Measurable g)
    (R : Ξ → ℝ) (hR : MemLp R 2 μ) (hbound : ∀ x z, ‖G x z‖ ≤ R z)
    (T : ℝ) (hgBound : ∀ x, ‖g x‖ ≤ T)
    (hmean : ∀ x, (∫ z, G x z ∂μ) = g x)
    (a b : (Fin (N+1) → Ξ) → Vec D) (ha : Measurable a) (hb : Measurable b)
    (B : ℝ) (hbBound : ∀ s, ‖b s‖ ≤ B) (i : Fin (N+1)) (z0 : Ξ)
    (haPast : ∀ s z, a (Function.update s i z) = a s)
    (hbPast : ∀ s z, b (Function.update s i z) = b s) :
    Integrable (fun s => inner ℝ (G (a s) (s i)-g (a s)) (b s)) (Measure.pi (fun _ : Fin (N+1) => μ)) ∧
      (∫ s, inner ℝ (G (a s) (s i)-g (a s)) (b s) ∂Measure.pi (fun _ : Fin (N+1) => μ)) = 0 := by
  have he := finite_oracle_error_memLp μ G g hG hg R hR hbound T hgBound a ha i
  have hem : Measurable (fun s : Fin (N+1) → Ξ => G (a s) (s i)-g (a s)) := by
    convert! (hG.comp (ha.prodMk (measurable_pi_apply i))).sub (hg.comp ha) using 1
  have hi : Integrable (fun s => inner ℝ (G (a s) (s i)-g (a s)) (b s))
      (Measure.pi (fun _ : Fin (N+1) => μ)) := by
    apply ((he.integrable (by norm_num)).norm.const_mul B).mono' (hem.inner hb).aestronglyMeasurable
    apply ae_of_all
    intro s
    calc
      _ ≤ ‖G (a s) (s i)-g (a s)‖*‖b s‖ := norm_inner_le_norm _ _
      _ ≤ B*‖G (a s) (s i)-g (a s)‖ := by nlinarith [norm_nonneg (G (a s) (s i)-g (a s)),hbBound s]
  refine ⟨hi,?_⟩
  apply finite_coordinate_centered_inner (fun _ : Fin (N+1) => μ) i a b G g z0 haPast hbPast _ hmean hi
  intro x
  have hm : Measurable (G x) := by convert! hG.comp (measurable_const.prodMk measurable_id) using 1
  exact (hR.mono' hm.aestronglyMeasurable (ae_of_all _ (hbound x))).integrable (by norm_num)
lemma finite_oracle_variance {Ξ : Type*} [MeasurableSpace Ξ] {D N : ℕ}
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (G : Vec D → Ξ → Vec D) (g : Vec D → Vec D)
    (hG : Measurable (Function.uncurry G)) (hg : Measurable g)
    (R : Ξ → ℝ) (hR : MemLp R 2 μ) (hbound : ∀ x z, ‖G x z‖ ≤ R z)
    (T : ℝ) (hgBound : ∀ x, ‖g x‖ ≤ T) (V : ℝ)
    (hvar : ∀ x, (∫ z, ‖G x z-g x‖^2 ∂μ) ≤ V)
    (a : (Fin (N+1) → Ξ) → Vec D) (ha : Measurable a) (i : Fin (N+1)) (z0 : Ξ)
    (haPast : ∀ s z, a (Function.update s i z) = a s) :
    Integrable (fun s => ‖G (a s) (s i)-g (a s)‖^2) (Measure.pi (fun _ : Fin (N+1) => μ)) ∧
      (∫ s, ‖G (a s) (s i)-g (a s)‖^2 ∂Measure.pi (fun _ : Fin (N+1) => μ)) ≤ V := by
  have he := finite_oracle_error_memLp μ G g hG hg R hR hbound T hgBound a ha i
  have hi := (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he
  refine ⟨hi,?_⟩
  exact finite_coordinate_expectation_le (fun _ : Fin (N+1) => μ) i a
    (fun x z => ‖G x z-g x‖^2) z0 haPast V hvar hi
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.UnitBallProjection
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def unitProjection {D : ℕ} (x : Vec D) : Vec D := (max 1 ‖x‖)⁻¹ • x
lemma unitProjection_continuous (D : ℕ) : Continuous (@unitProjection D) := by
  have hscalar : Continuous (fun x : Vec D => (max 1 ‖x‖)⁻¹) := by
    apply Continuous.inv₀ (continuous_const.max continuous_norm)
    intro x
    have : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact this.ne'
  convert! hscalar.smul (continuous_id : Continuous (fun x : Vec D => x)) using 1
lemma unitProjection_norm {D : ℕ} (x : Vec D) : ‖unitProjection x‖ ≤ 1 := by
  have hm : 0 < max (1 : ℝ) ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitProjection,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hm.le),
    inv_mul_le_iff₀ hm]
  simpa using le_max_right (1 : ℝ) ‖x‖
lemma unitProjection_of_norm_le {D : ℕ} (x : Vec D) (hx : ‖x‖ ≤ 1) : unitProjection x = x := by
  simp [unitProjection,max_eq_left hx]
lemma unitProjection_distance {D : ℕ} (x : Vec D) (hx : 1 < ‖x‖) :
    ‖unitProjection x-x‖ = ‖x‖-1 := by
  have hp : 0 < ‖x‖ := lt_trans zero_lt_one hx
  have hi : ‖x‖⁻¹ ≤ 1 := by apply (inv_le_one₀ hp).mpr; exact hx.le
  have he : ‖x‖⁻¹ • x - x = (‖x‖⁻¹-1) • x := by rw [sub_smul,one_smul]
  rw [unitProjection,max_eq_right hx.le,he,norm_smul,
    Real.norm_eq_abs,abs_of_nonpos (by linarith : ‖x‖⁻¹-1 ≤ 0)]
  field_simp
  ring
lemma unitProjection_isProjection (D : ℕ) :
    IsProjection D (Metric.closedBall 0 1) (@unitProjection D) := by
  intro x
  refine ⟨?_,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using unitProjection_norm x
  · intro w hw
    have hw' : ‖w‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
    by_cases hx : ‖x‖ ≤ 1
    · rw [unitProjection_of_norm_le x hx,sub_self,norm_zero]
      exact norm_nonneg _
    · rw [unitProjection_distance x (lt_of_not_ge hx)]
      have h := norm_sub_norm_le x w
      rw [norm_sub_rev x w] at h
      linarith
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.FiniteProjectedOptimizer
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
open NonconvexAG.StochComposite
lemma finite_projected_optimizer_utility {D N : ℕ} (hN : 1 ≤ N)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ] (z0 : Ξ)
    (F : Vec D → ℝ) (g : Vec D → Vec D) (L : ℝ)
    (hsmooth : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L) (hconv : ConvexOn ℝ univ F)
    (hF : Measurable F) (hg : Measurable g) (K T : ℝ)
    (hFbound : ∀ v, ‖v‖ ≤ 1 → |F v| ≤ K) (hgBound : ∀ v, ‖g v‖ ≤ T)
    (G : Vec D → Ξ → Vec D) (hG : Measurable (Function.uncurry G))
    (R : Ξ → ℝ) (hR : MemLp R 2 μ) (hGbound : ∀ v z, ‖G v z‖ ≤ R z)
    (hmean : ∀ v, (∫ z, G v z ∂μ) = g v) (σ β : ℝ)
    (hvar : ∀ v, (∫ z, ‖G v z-g v‖^2 ∂μ) ≤ σ^2)
    (hβ : 0 < β) (hLβ : L*β ≤ 1/2) (vstar : Vec D) (hvstar : ‖vstar‖ ≤ 1) :
    let ξ := fun k (s : Fin (N+1) → Ξ) => finiteNoiseSequence z0 s k
    let out := xagSeq G (fun x y c => unitProjection (x-c • y)) accelAlpha
      (fun _ => β) (accelLambda β) (fun _ => 1) 0 ξ N
    Integrable (fun s => F (out s)-F vstar) (Measure.pi (fun _ : Fin (N+1) => μ)) ∧
      (∫ s, F (out s)-F vstar ∂Measure.pi (fun _ : Fin (N+1) => μ)) ≤
        NonconvexAG.Smooth.Gamma accelAlpha N * (‖vstar‖^2/β) + 3*σ^2*β*N := by
  let ξ := fun k (s : Fin (N+1) → Ξ) => finiteNoiseSequence z0 s k
  let P := fun (x y : Vec D) (c : ℝ) => unitProjection (x-c • y)
  let path := fun k (s : Fin (N+1) → Ξ) =>
    rsagPath G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0 (fun j => ξ j s) k
  have hP : Measurable (fun q : (Vec D × Vec D) × ℝ => P q.1.1 q.1.2 q.2) := by
    apply (unitProjection_continuous D).measurable.comp
    fun_prop
  have hpath (k : ℕ) : Measurable (path k) :=
    rsagPath_one_measurable G hG P hP accelAlpha (fun _ => β) (accelLambda β) 0 ξ
      (fun k => finiteNoiseSequence_measurable z0 k) k
  have hnorm (k : ℕ) (s : Fin (N+1) → Ξ) : ‖(path k s).1‖ ≤ 1 ∧ ‖(path k s).2‖ ≤ 1 := by
    have h := rsagPath_projected_mem G (Metric.closedBall 0 1) unitProjection
      (fun x => (unitProjection_isProjection D x).1)
      accelAlpha (fun _ => β) (accelLambda β) 0 (by simp) (fun j => ξ j s) k
    simpa only [Metric.mem_closedBall,dist_zero_right] using h
  have hgap : Integrable (fun s => F ((path N s).2)-F vstar) (Measure.pi (fun _ : Fin (N+1) => μ)) := by
    apply (integrable_const (K+|F vstar|)).mono'
      ((hF.comp (hpath N).snd).sub measurable_const).aestronglyMeasurable
    apply ae_of_all
    intro s
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hFbound _ (hnorm N s).2) le_rfl)
  have hcross : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun s => inner ℝ (deltaBar G g P accelAlpha (fun _ => β) (accelLambda β)
        (fun _ => 1) 0 ξ k s) (vstar-(path (k-1) s).1)) (Measure.pi (fun _ : Fin (N+1) => μ)) ∧
      (∫ s, inner ℝ (deltaBar G g P accelAlpha (fun _ => β) (accelLambda β)
        (fun _ => 1) 0 ξ k s) (vstar-(path (k-1) s).1) ∂Measure.pi (fun _ : Fin (N+1) => μ)) = 0 := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hkN := (mem_Icc.mp hk).2
    let i : Fin (N+1) := ⟨k,by omega⟩
    let a := xmdSeq G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0 ξ k
    let b := fun s => vstar-(path (k-1) s).1
    have ha : Measurable a := by
      convert! ((hpath (k-1)).snd.const_smul (1-accelAlpha k)).add
        ((hpath (k-1)).fst.const_smul (accelAlpha k)) using 1
    have hb : Measurable b := by convert! measurable_const.sub (hpath (k-1)).fst using 1
    have hbBound (s) : ‖b s‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by linarith [(hnorm (k-1) s).1])
    have haPast (s) (z) : a (Function.update s i z) = a s :=
      xmdSeq_finite_update G P accelAlpha (fun _ => β) (accelLambda β) 0 z0 z s i hk1
    have hbPast (s) (z) : b (Function.update s i z) = b s := by
      have h := rsagPath_finite_update G P accelAlpha (fun _ => β) (accelLambda β) 0 z0 z s i (k-1) (by dsimp [i]; omega)
      change vstar-(rsagPath G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0
        (finiteNoiseSequence z0 (Function.update s i z)) (k-1)).1 = _
      rw [h]
    have h := finite_oracle_cross_moment μ G g hG hg R hR hGbound T hgBound hmean
      a b ha hb 2 hbBound i z0 haPast hbPast
    convert! h using 1 <;>
      simp only [deltaBar_one G g P accelAlpha (fun _ => β) (accelLambda β) 0 ξ k hk1,
        a,b,ξ,i,finiteNoiseSequence_apply z0 _ k hkN]
  have hvarRun : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun s => ‖deltaBar G g P accelAlpha (fun _ => β) (accelLambda β)
        (fun _ => 1) 0 ξ k s‖^2) (Measure.pi (fun _ : Fin (N+1) => μ)) ∧
      (∫ s, ‖deltaBar G g P accelAlpha (fun _ => β) (accelLambda β)
        (fun _ => 1) 0 ξ k s‖^2 ∂Measure.pi (fun _ : Fin (N+1) => μ)) ≤ σ^2 := by
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hkN := (mem_Icc.mp hk).2
    let i : Fin (N+1) := ⟨k,by omega⟩
    let a := xmdSeq G P accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0 ξ k
    have ha : Measurable a := by
      convert! ((hpath (k-1)).snd.const_smul (1-accelAlpha k)).add
        ((hpath (k-1)).fst.const_smul (accelAlpha k)) using 1
    have haPast (s) (z) : a (Function.update s i z) = a s :=
      xmdSeq_finite_update G P accelAlpha (fun _ => β) (accelLambda β) 0 z0 z s i hk1
    have h := finite_oracle_variance μ G g hG hg R hR hGbound T hgBound (σ^2) hvar a ha i z0 haPast
    convert! h using 1 <;>
      simp only [deltaBar_one G g P accelAlpha (fun _ => β) (accelLambda β) 0 ξ k hk1,
        a,ξ,i,finiteNoiseSequence_apply z0 _ k hkN]
  refine ⟨hgap,?_⟩
  have h := accelerated_projected_finite_utility F g L hsmooth hconv
    (Metric.closedBall 0 1) (convex_closedBall (0 : Vec D) 1) unitProjection (unitProjection_isProjection D)
    G (Measure.pi (fun _ : Fin (N+1) => μ)) ξ σ β hβ hLβ 0 N hN vstar
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hvstar) hgap hcross hvarRun
  simpa only [zero_sub,norm_neg] using h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.EuclideanVariance
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def euclideanVariance {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) (f : Z → Vec D) : ℝ := ∫ z, ‖f z-∫ x, f x ∂μ‖^2 ∂μ
lemma euclidean_coordinate_memLp {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) (f : Z → Vec D) (hf : MemLp f 2 μ) (j : Fin D) :
    MemLp (fun z => f z j) 2 μ := by
  simpa only [Function.comp_def,EuclideanSpace.coe_proj] using
    (EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' hf
lemma euclidean_integral_coordinate {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) (f : Z → Vec D) (hf : Integrable f μ) (j : Fin D) :
    (∫ z, f z ∂μ) j = ∫ z, f z j ∂μ := by
  simpa only [Function.comp_def,EuclideanSpace.coe_proj] using
    ((EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hf).symm
lemma euclideanVariance_smul {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) (f : Z → Vec D) (c : ℝ) :
    euclideanVariance μ (fun z => c • f z) = c^2 * euclideanVariance μ f := by
  unfold euclideanVariance
  rw [integral_smul]
  simp_rw [← smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  exact integral_const_mul _ _
lemma euclideanVariance_eq_sum {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → Vec D) (hf : MemLp f 2 μ) :
    euclideanVariance μ f = ∑ j : Fin D, variance (fun z => f z j) μ := by
  have hcent := hf.sub (memLp_const (∫ z, f z ∂μ))
  have hi (j : Fin D) : Integrable (fun z => (f z - ∫ x, f x ∂μ) j ^ 2) μ := by
    simpa only [Pi.sub_apply] using (euclidean_coordinate_memLp μ _ hcent j).integrable_sq
  unfold euclideanVariance
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum univ (fun j _ => hi j)]
  apply sum_congr rfl
  intro j hj
  simp_rw [PiLp.sub_apply]
  rw [variance_eq_integral (euclidean_coordinate_memLp μ f hf j).aestronglyMeasurable.aemeasurable,
    euclidean_integral_coordinate μ f (hf.integrable (by norm_num)) j]
lemma euclideanVariance_le_second_moment {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → Vec D) (hf : MemLp f 2 μ) :
    euclideanVariance μ f ≤ ∫ z, ‖f z‖^2 ∂μ := by
  rw [euclideanVariance_eq_sum μ f hf]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum univ (fun j _ => (euclidean_coordinate_memLp μ f hf j).integrable_sq)]
  apply sum_le_sum
  intro j hj
  exact variance_le_expectation_sq (euclidean_coordinate_memLp μ f hf j).aestronglyMeasurable
lemma euclideanVariance_le_of_bounded {Z : Type*} [MeasurableSpace Z] {D : ℕ}
    (μ : Measure Z) [IsProbabilityMeasure μ] (f : Z → Vec D) (hf : Measurable f)
    (T : ℝ) (hT : 0 ≤ T) (hbound : ∀ z, ‖f z‖ ≤ T) : euclideanVariance μ f ≤ T^2 := by
  have hmem : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable T (ae_of_all _ hbound)
  apply (euclideanVariance_le_second_moment μ f hmem).trans
  calc
    _ ≤ ∫ _ : Z, T^2 ∂μ := by
      apply integral_mono (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable |>.mp hmem) (integrable_const _)
      intro z
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound z) 2
    _ = _ := by simp
lemma euclideanVariance_sum_pi {ι : Type*} [Fintype ι] {D : ℕ}
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ι → ℝ → Vec D) (hf : ∀ i, MemLp (f i) 2 (μ i)) :
    euclideanVariance (Measure.pi μ) (fun z => ∑ i, f i (z i)) =
      ∑ i, euclideanVariance (μ i) (f i) := by
  have hcomp (i : ι) : MemLp (fun z : ι → ℝ => f i (z i)) 2 (Measure.pi μ) := by
    simpa only [Function.comp_def] using (hf i).comp_measurePreserving (measurePreserving_eval μ i)
  have hsum : MemLp (fun z : ι → ℝ => ∑ i, f i (z i)) 2 (Measure.pi μ) :=
    memLp_finsetSum univ (fun i _ => hcomp i)
  rw [euclideanVariance_eq_sum _ _ hsum]
  simp_rw [euclideanVariance_eq_sum _ _ (hf _)]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have he : (fun z : ι → ℝ => (∑ i, f i (z i)) j) = (fun z => ∑ i, f i (z i) j) := by
    funext z
    exact map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) (fun i => f i (z i)) univ
  rw [he]
  have h := variance_sum_pi (fun i => euclidean_coordinate_memLp (μ i) (f i) (hf i) j)
  convert! h using 2
  ext z
  simp only [Finset.sum_apply]
lemma euclideanVariance_average_pi_le {D n : ℕ} (hn : 0 < n)
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : Fin n → ℝ → Vec D) (hf : ∀ i, MemLp (f i) 2 (μ i))
    (V : ℝ) (hV : ∀ i, euclideanVariance (μ i) (f i) ≤ V) :
    euclideanVariance (Measure.pi μ) (fun z => (n : ℝ)⁻¹ • ∑ i, f i (z i)) ≤ V/(n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [euclideanVariance_smul,euclideanVariance_sum_pi μ f hf]
  calc
    _ ≤ (n : ℝ)⁻¹^2 * ∑ _i : Fin n, V :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hV i)) (sq_nonneg _)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.ThresholdTranslation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def thresholdStep (θ x : ℝ) : ℝ := if θ ≤ x then 1 else -1
lemma thresholdStep_measurable (θ : ℝ) : Measurable (thresholdStep θ) := by
  unfold thresholdStep
  exact measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const
lemma thresholdStep_abs (θ x : ℝ) : |thresholdStep θ x| = 1 := by
  unfold thresholdStep; split_ifs <;> norm_num
lemma thresholdStep_difference_bound (θ η x : ℝ) :
    |thresholdStep θ x - thresholdStep η x| ≤
      (uIcc θ η).indicator (fun _ => (2 : ℝ)) x := by
  unfold thresholdStep
  by_cases hθ : θ ≤ x <;> by_cases hη : η ≤ x
  · simp only [if_pos hθ, if_pos hη, sub_self, abs_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) x
  · have hx : x ∈ uIcc θ η := by
      simp only [mem_uIcc]
      exact Or.inl ⟨hθ, (lt_of_not_ge hη).le⟩
    norm_num [hθ, hη, hx]
  · have hx : x ∈ uIcc θ η := by
      simp only [mem_uIcc]
      exact Or.inr ⟨hη, (lt_of_not_ge hθ).le⟩
    norm_num [hθ, hη, hx]
  · simp only [if_neg hθ, if_neg hη, sub_self, abs_zero]
    exact indicator_nonneg (fun _ _ => by norm_num) x
lemma gaussianPDF_standard_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ (Real.sqrt (2*Real.pi))⁻¹ := by
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
lemma gaussian_threshold_translation (θ η : ℝ) :
    (∫ x, |thresholdStep θ x - thresholdStep η x| ∂gaussianReal 0 1) ≤
      2 * (Real.sqrt (2*Real.pi))⁻¹ * |θ-η| := by
  have hm : Measurable (fun x => |thresholdStep θ x - thresholdStep η x|) :=
    ((thresholdStep_measurable θ).sub (thresholdStep_measurable η)).abs
  have hb (x : ℝ) : |thresholdStep θ x - thresholdStep η x| ≤ 2 := by
    calc
      _ ≤ |thresholdStep θ x| + |thresholdStep η x| := abs_sub _ _
      _ = _ := by rw [thresholdStep_abs, thresholdStep_abs]; norm_num
  have hi : Integrable (fun x => gaussianPDFReal 0 1 x *
      |thresholdStep θ x - thresholdStep η x|) := by
    apply ((integrable_gaussianPDFReal 0 1).const_mul 2).mono' (by fun_prop)
    exact ae_of_all volume (fun x => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _),
        abs_abs]
      nlinarith [gaussianPDFReal_nonneg 0 1 x, hb x])
  have hj : Integrable ((uIcc θ η).indicator
      (fun _ => 2 * (Real.sqrt (2*Real.pi))⁻¹)) volume := by
    exact integrableOn_const isCompact_uIcc.measure_ne_top |>.integrable_indicator measurableSet_uIcc
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  calc
    _ ≤ ∫ x, (uIcc θ η).indicator
        (fun _ => 2 * (Real.sqrt (2*Real.pi))⁻¹) x := by
      apply integral_mono hi hj
      intro x
      have hs := thresholdStep_difference_bound θ η x
      by_cases hx : x ∈ uIcc θ η
      · simp only [indicator_of_mem hx, smul_eq_mul]
        calc
          _ ≤ gaussianPDFReal 0 1 x * 2 :=
            mul_le_mul_of_nonneg_left (hb x) (gaussianPDFReal_nonneg _ _ _)
          _ ≤ _ := by linarith [gaussianPDF_standard_le x]
      · simp only [indicator_of_notMem hx] at hs ⊢
        rw [le_antisymm hs (abs_nonneg _), mul_zero]
    _ = _ := by simp [integral_indicator, measurableSet_uIcc, integral_const,
      abs_sub_comm, mul_comm]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.L2Integral
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma norm_toLp_two_sq {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (f : Z → ℝ)
    (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ z, f z^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]
  change f z * f z = f z^2
  ring
lemma integral_abs_le_norm_toLp {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (f : Z → ℝ) (hf : MemLp f 2 μ) :
    (∫ z, |f z| ∂μ) ≤ ‖hf.toLp f‖ := by
  have hi := (hf.integrable (by norm_num)).norm
  have hsq : Integrable ((fun x : ℝ => x^2) ∘ (fun z => |f z|)) μ := by
    simpa [Function.comp_def, sq_abs] using hf.integrable_sq
  have h := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le (continuous_pow 2).continuousOn
    isClosed_Ici (ae_of_all μ (fun z => abs_nonneg (f z))) (by
      simpa [Real.norm_eq_abs] using hi) hsq
  simp only [Function.comp_def, sq_abs] at h
  rw [← norm_toLp_two_sq μ f hf] at h
  exact (sq_le_sq₀ (integral_nonneg (fun z => abs_nonneg _)) (norm_nonneg _)).mp h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianAbsoluteSmoothing
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
local instance : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
noncomputable def smoothAbs (s b : ℝ) : ℝ := ∫ z, |b+s*z| ∂gaussianReal 0 1
noncomputable def smoothAbsSlope (s b : ℝ) : ℝ :=
  ∫ z, thresholdStep 0 (b+s*z) ∂gaussianReal 0 1
lemma smoothAbs_integrable (s b : ℝ) : Integrable (fun z => |b+s*z|) (gaussianReal 0 1) := by
  have hi := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  simpa [id_eq, Real.norm_eq_abs] using ((integrable_const b).add (hi.const_mul s)).norm
lemma smoothAbsSlope_integrable (s b : ℝ) :
    Integrable (fun z => thresholdStep 0 (b+s*z)) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((thresholdStep_measurable 0).comp (by fun_prop)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simp [Real.norm_eq_abs,thresholdStep_abs])
lemma smoothAbs_hasDerivAt (s : ℝ) (hs : 0 < s) (b : ℝ) :
    HasDerivAt (smoothAbs s) (smoothAbsSlope s b) b := by
  have hz : ∀ᵐ z ∂gaussianReal 0 1, z ≠ -b/s := by
    simpa only [ae_iff,not_not,Set.setOf_eq_eq_singleton] using
      (measure_singleton (-b/s) : (gaussianReal 0 1) {-b/s} = 0)
  have hdiff : ∀ᵐ z ∂gaussianReal 0 1,
      HasDerivAt (fun u : ℝ => |u+s*z|) (thresholdStep 0 (b+s*z)) b := by
    filter_upwards [hz] with z hz
    have hn : b+s*z ≠ 0 := by intro he; apply hz; apply (eq_div_iff hs.ne').mpr; nlinarith
    by_cases hp : 0 < b+s*z
    · convert! (hasDerivAt_abs_pos hp).comp b ((hasDerivAt_id b).add_const (s*z)) using 1 <;>
        simp [thresholdStep,hp.le,Function.comp_def]
    · have hm : b+s*z < 0 := lt_of_le_of_ne (le_of_not_gt hp) hn
      convert! (hasDerivAt_abs_neg hm).comp b ((hasDerivAt_id b).add_const (s*z)) using 1 <;>
        simp [thresholdStep, not_le.mpr hm,Function.comp_def]
  have hlip (z : ℝ) : LipschitzWith 1 (fun u : ℝ => |u+s*z|) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [NNReal.coe_one,one_mul,Real.dist_eq]
    apply (abs_abs_sub_abs_le_abs_sub _ _).trans_eq
    congr 1
    ring
  have hone : Real.nnabs (1 : ℝ) = (1 : ℝ≥0) := by
    apply NNReal.coe_injective
    change |(1 : ℝ)| = 1
    norm_num
  have h := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := gaussianReal 0 1) (F := fun u z : ℝ => |u+s*z|)
    (F' := fun z => thresholdStep 0 (b+s*z)) (bound := fun _ => (1 : ℝ))
    (s := univ) (x₀ := b) univ_mem
    (Eventually.of_forall (fun u => by fun_prop)) (smoothAbs_integrable s b)
    ((thresholdStep_measurable 0).comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ (fun z => by simpa only [hone,lipschitzOnWith_univ] using hlip z))
    (integrable_const 1) hdiff
  exact h.2
lemma standardGaussian_abs_mean_le_one : (∫ z : ℝ, |z| ∂gaussianReal 0 1) ≤ 1 := by
  have hm : MemLp (fun z : ℝ => z) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal (μ := 0) (v := 1) 2
  have hsq : (∫ z : ℝ, z^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at h
    simpa [id_eq,integral_id_gaussianReal] using h
  have hn := norm_toLp_two_sq (gaussianReal 0 1) _ hm
  rw [hsq] at hn
  have hb := integral_abs_le_norm_toLp (gaussianReal 0 1) _ hm
  have hp := norm_nonneg (hm.toLp (fun z : ℝ => z))
  nlinarith
lemma smoothAbs_approx (s b : ℝ) (hs : 0 ≤ s) : abs (smoothAbs s b-abs b) ≤ s := by
  have hi := smoothAbs_integrable s b
  have hz := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have he : smoothAbs s b-|b| = ∫ z, |b+s*z|-|b| ∂gaussianReal 0 1 := by
    rw [integral_sub hi (integrable_const _),integral_const]
    simp [smoothAbs]
  rw [he,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, ‖|b+s*z|-|b|‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ z, s*|z| ∂gaussianReal 0 1 := by
      apply integral_mono ((hi.sub (integrable_const _)).norm) (hz.norm.const_mul s)
      intro z
      change ‖(|b+s*z|-|b|)‖ ≤ s*‖z‖
      simp only [Real.norm_eq_abs]
      calc
        _ ≤ |(b+s*z)-b| := abs_abs_sub_abs_le_abs_sub _ _
        _ = _ := by rw [add_sub_cancel_left,abs_mul,abs_of_nonneg hs]
    _ = s*(∫ z : ℝ, |z| ∂gaussianReal 0 1) := integral_const_mul _ _
    _ ≤ s := mul_le_of_le_one_right hs standardGaussian_abs_mean_le_one
lemma abs_le_smoothAbs (s b : ℝ) : |b| ≤ smoothAbs s b := by
  have hz := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have h := norm_integral_le_integral_norm (μ := gaussianReal 0 1) (fun z => b+s*z)
  have he : (∫ z : ℝ, b+s*z ∂gaussianReal 0 1) = b := by
    rw [integral_add (integrable_const b) (show Integrable (fun z : ℝ => s*z) (gaussianReal 0 1) from hz.const_mul s)]
    rw [integral_const_mul,integral_id_gaussianReal,integral_const]
    simp
  rw [he] at h
  simpa [smoothAbs,Real.norm_eq_abs] using h
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.GaussianAbsoluteSlope
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma thresholdStep_integrable (θ : ℝ) : Integrable (thresholdStep θ) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono' (thresholdStep_measurable θ).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simp [Real.norm_eq_abs,thresholdStep_abs])
lemma gaussian_standard_density_constant_le_one : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := by
  have hp : 0 < 2*Real.pi := by positivity
  have hsq := Real.sq_sqrt hp.le
  have hn := Real.sqrt_nonneg (2*Real.pi)
  have hge : 1 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.pi_gt_three]
  rw [← one_div]
  exact (div_le_one (Real.sqrt_pos.mpr hp)).mpr hge
lemma gaussian_threshold_translation_simple (θ η : ℝ) :
    (∫ z, |thresholdStep θ z-thresholdStep η z| ∂gaussianReal 0 1) ≤ 2*|θ-η| := by
  apply (gaussian_threshold_translation θ η).trans
  nlinarith [mul_le_mul_of_nonneg_right gaussian_standard_density_constant_le_one (abs_nonneg (θ-η))]
lemma smoothAbsSlope_threshold (s b : ℝ) (hs : 0 < s) :
    smoothAbsSlope s b = ∫ z, thresholdStep (-b/s) z ∂gaussianReal 0 1 := by
  unfold smoothAbsSlope
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    unfold thresholdStep
    have he : (0 ≤ b+s*z) ↔ -b/s ≤ z := by
      rw [div_le_iff₀ hs]
      constructor <;> intro h <;> nlinarith
    exact if_congr he rfl rfl)
lemma smoothAbsSlope_lipschitz_bound (s : ℝ) (hs : 0 < s) (b c : ℝ) :
    |smoothAbsSlope s b-smoothAbsSlope s c| ≤ (2/s)*|b-c| := by
  rw [smoothAbsSlope_threshold s b hs,smoothAbsSlope_threshold s c hs,
    ← integral_sub (thresholdStep_integrable _) (thresholdStep_integrable _),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ z, ‖thresholdStep (-b/s) z-thresholdStep (-c/s) z‖ ∂gaussianReal 0 1 :=
      norm_integral_le_integral_norm _
    _ ≤ 2*|(-b/s)-(-c/s)| := by
      simpa only [Real.norm_eq_abs] using gaussian_threshold_translation_simple (-b/s) (-c/s)
    _ = _ := by
      rw [show (-b/s)-(-c/s) = -(b-c)/s by ring,abs_div,abs_neg,abs_of_pos hs]
      ring
lemma smoothAbsSlope_abs_le_one (s b : ℝ) : |smoothAbsSlope s b| ≤ 1 := by
  unfold smoothAbsSlope
  have h := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
    (f := fun z => thresholdStep 0 (b+s*z)) (C := 1)
    (ae_of_all _ (fun z => by simp [Real.norm_eq_abs,thresholdStep_abs]))
  simpa [Real.norm_eq_abs] using h
lemma smoothAbsSlope_continuous (s : ℝ) (hs : 0 < s) : Continuous (smoothAbsSlope s) := by
  have hl : LipschitzWith (Real.toNNReal (2/s)) (smoothAbsSlope s) := by
    apply LipschitzWith.of_dist_le_mul
    intro b c
    simpa only [Real.dist_eq,Real.coe_toNNReal _ (by positivity : 0 ≤ 2/s)] using
      smoothAbsSlope_lipschitz_bound s hs b c
  exact hl.continuous
lemma smoothAbs_contDiff_one (s : ℝ) (hs : 0 < s) : ContDiff ℝ 1 (smoothAbs s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun b => (smoothAbs_hasDerivAt s hs b).differentiableAt,?_⟩
  have he : deriv (smoothAbs s) = smoothAbsSlope s := funext (fun b => (smoothAbs_hasDerivAt s hs b).deriv)
  rw [he]
  exact smoothAbsSlope_continuous s hs
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.RegressionOracleGeometry
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
noncomputable def absoluteLinearLoss (a : E) (y : ℝ) (v : E) : ℝ := |inner ℝ v a-y|
noncomputable def absoluteLinearSubgradient (a : E) (y : ℝ) (v : E) : E :=
  if 0 ≤ inner ℝ v a-y then a else -a
lemma absoluteLinearSubgradient_norm (a : E) (y : ℝ) (v : E) :
    ‖absoluteLinearSubgradient a y v‖ = ‖a‖ := by
  unfold absoluteLinearSubgradient
  split_ifs <;> simp
lemma absoluteLinearSubgradient_valid (a : E) (y : ℝ) (v w : E) :
    absoluteLinearLoss a y v + inner ℝ (absoluteLinearSubgradient a y v) (w-v) ≤
      absoluteLinearLoss a y w := by
  have hi : inner ℝ a (w-v) = (inner ℝ w a-y)-(inner ℝ v a-y) := by
    rw [show inner ℝ a (w-v) = inner ℝ (w-v) a from real_inner_comm _ _, inner_sub_left]
    ring
  unfold absoluteLinearSubgradient absoluteLinearLoss
  split_ifs with h
  · rw [abs_of_nonneg h, hi]
    linarith [le_abs_self (inner ℝ w a-y)]
  · rw [abs_of_neg (lt_of_not_ge h), inner_neg_left, hi]
    linarith [neg_le_abs (inner ℝ w a-y)]
lemma absoluteLinearLoss_convex (a : E) (y : ℝ) : ConvexOn ℝ univ (absoluteLinearLoss a y) := by
  refine ⟨convex_univ,?_⟩
  intro v hv w hw r s hr hs hrs
  unfold absoluteLinearLoss
  simp only [inner_add_left, inner_smul_left, conj_trivial, smul_eq_mul]
  have he : r*inner ℝ v a+s*inner ℝ w a-y =
      r*(inner ℝ v a-y)+s*(inner ℝ w a-y) := by linear_combination y * hrs
  rw [he]
  calc
    _ ≤ |r*(inner ℝ v a-y)|+|s*(inner ℝ w a-y)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg hr,abs_of_nonneg hs]
lemma absoluteLinearLoss_lipschitz (a : E) (y : ℝ) :
    LipschitzWith ‖a‖₊ (absoluteLinearLoss a y) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq]
  change abs (abs (inner ℝ v a-y) - abs (inner ℝ w a-y)) ≤ ‖a‖*dist v w
  calc
    _ ≤ |(inner ℝ v a-y)-(inner ℝ w a-y)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = ‖inner ℝ (v-w) a‖ := by rw [inner_sub_left, Real.norm_eq_abs]; congr 1; ring
    _ ≤ ‖v-w‖*‖a‖ := norm_inner_le_norm _ _
    _ = _ := by rw [dist_eq_norm]; ring
lemma measurable_absoluteLinearSubgradient {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (a : Z → E) (y : Z → ℝ) (ha : Measurable a) (hy : Measurable y) :
    Measurable (fun z : Z × E => absoluteLinearSubgradient (a z.1) (y z.1) z.2) := by
  unfold absoluteLinearSubgradient
  exact (ha.comp measurable_fst).ite
    (measurableSet_le measurable_const ((measurable_snd.inner (ha.comp measurable_fst)).sub
      (hy.comp measurable_fst))) (ha.comp measurable_fst).neg
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedRegressionLoss
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
noncomputable def smoothedLinearLoss (r : ℝ) (a : E) (y : ℝ) (v : E) : ℝ :=
  smoothAbs (r*‖a‖) (inner ℝ v a-y)
noncomputable def smoothedLinearGradient (r : ℝ) (a : E) (y : ℝ) (v : E) : E :=
  smoothAbsSlope (r*‖a‖) (inner ℝ v a-y) • a
lemma smoothedLinearLoss_hasGradient (r : ℝ) (hr : 0 < r) (a : E) (y : ℝ) (v : E) :
    HasGradientAt (smoothedLinearLoss r a y) (smoothedLinearGradient r a y v) v := by
  by_cases ha : a = 0
  · subst a
    have he : smoothedLinearLoss r (0 : E) y = fun _ => smoothAbs 0 (-y) := by
      funext w
      simp [smoothedLinearLoss]
    rw [he]
    simpa only [smoothedLinearGradient,smul_zero] using (hasGradientAt_const v (smoothAbs 0 (-y)))
  · have hs : 0 < r*‖a‖ := mul_pos hr (norm_pos_iff.mpr ha)
    have hlin : HasFDerivAt (fun v : E => inner ℝ v a-y) (innerSL ℝ a) v := by
      convert! (innerSL ℝ a).hasFDerivAt.sub_const y using 1
      funext w
      rw [real_inner_comm]
      rfl
    have h := (smoothAbs_hasDerivAt (r*‖a‖) hs (inner ℝ v a-y)).hasFDerivAt.comp v hlin
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! h using 1
    ext w
    simp [smoothedLinearGradient,InnerProductSpace.toDual_apply_apply,inner_smul_left,mul_comm]
lemma smoothedLinearLoss_convex (r : ℝ) (a : E) (y : ℝ) :
    ConvexOn ℝ univ (smoothedLinearLoss r a y) := by
  refine ⟨convex_univ,?_⟩
  intro v hv w hw c e hc he hce
  have hvint := smoothAbs_integrable (r*‖a‖) (inner ℝ v a-y)
  have hwint := smoothAbs_integrable (r*‖a‖) (inner ℝ w a-y)
  change (∫ z, |inner ℝ (c • v+e • w) a-y+r*‖a‖*z| ∂gaussianReal 0 1) ≤ _
  have hpoint (z : ℝ) : |inner ℝ (c • v+e • w) a-y+r*‖a‖*z| ≤
      c*|inner ℝ v a-y+r*‖a‖*z|+e*|inner ℝ w a-y+r*‖a‖*z| := by
    have h := (absoluteLinearLoss_convex a (y-r*‖a‖*z)).2 hv hw hc he hce
    simpa only [absoluteLinearLoss,sub_eq_add_neg,neg_add_rev,neg_neg,add_assoc,add_left_comm,add_comm,smul_eq_mul] using h
  have hm := integral_mono (smoothAbs_integrable (r*‖a‖) (inner ℝ (c • v+e • w) a-y))
    ((hvint.const_mul c).add (hwint.const_mul e)) hpoint
  change (∫ z, |inner ℝ (c • v+e • w) a-y+r*‖a‖*z| ∂gaussianReal 0 1) ≤
    (∫ z, c*|inner ℝ v a-y+r*‖a‖*z|+e*|inner ℝ w a-y+r*‖a‖*z| ∂gaussianReal 0 1) at hm
  rw [integral_add (hvint.const_mul c) (hwint.const_mul e),integral_const_mul,integral_const_mul] at hm
  exact hm
lemma smoothedLinearLoss_approx (r : ℝ) (hr : 0 ≤ r) (a : E) (y : ℝ) (v : E) :
    absoluteLinearLoss a y v ≤ smoothedLinearLoss r a y v ∧
      smoothedLinearLoss r a y v ≤ absoluteLinearLoss a y v+r*‖a‖ := by
  refine ⟨abs_le_smoothAbs _ _,?_⟩
  have h := smoothAbs_approx (r*‖a‖) (inner ℝ v a-y) (mul_nonneg hr (norm_nonneg _))
  unfold absoluteLinearLoss smoothedLinearLoss
  linarith [le_abs_self (smoothAbs (r*‖a‖) (inner ℝ v a-y)-|inner ℝ v a-y|)]
lemma smoothedLinearGradient_lipschitz (r : ℝ) (hr : 0 < r) (a : E) (y : ℝ) (v w : E) :
    ‖smoothedLinearGradient r a y v-smoothedLinearGradient r a y w‖ ≤
      (2*‖a‖/r)*‖v-w‖ := by
  by_cases ha : a = 0
  · subst a; simp [smoothedLinearGradient]
  · have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hs : 0 < r*‖a‖ := mul_pos hr hn
    have hb := smoothAbsSlope_lipschitz_bound (r*‖a‖) hs (inner ℝ v a-y) (inner ℝ w a-y)
    have hinner : |(inner ℝ v a-y)-(inner ℝ w a-y)| ≤ ‖v-w‖*‖a‖ := by
      have he : (inner ℝ v a-y)-(inner ℝ w a-y) = inner ℝ (v-w) a := by rw [inner_sub_left]; ring
      rw [he,← Real.norm_eq_abs]
      exact norm_inner_le_norm _ _
    unfold smoothedLinearGradient
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (2/(r*‖a‖))*|(inner ℝ v a-y)-(inner ℝ w a-y)| *‖a‖ := by gcongr
      _ ≤ (2/(r*‖a‖))*(‖v-w‖*‖a‖)*‖a‖ := by gcongr
      _ = _ := by field_simp [hr.ne',hn.ne'] <;> ring
lemma smoothedLinearGradient_norm (r : ℝ) (a : E) (y : ℝ) (v : E) :
    ‖smoothedLinearGradient r a y v‖ ≤ ‖a‖ := by
  rw [smoothedLinearGradient,norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (smoothAbsSlope_abs_le_one _ _)
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedEmpiricalRegression
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
noncomputable def linearEmpirical {n : ℕ} (a : Fin n → E) (y : Fin n → ℝ) (v : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, absoluteLinearLoss (a i) (y i) v
noncomputable def smoothedEmpirical {n : ℕ} (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) (v : E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, smoothedLinearLoss r (a i) (y i) v
noncomputable def smoothedEmpiricalGradient {n : ℕ} (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) (v : E) : E :=
  (n : ℝ)⁻¹ • ∑ i, smoothedLinearGradient r (a i) (y i) v
lemma smoothedEmpirical_hasGradient {n : ℕ} (r : ℝ) (hr : 0 < r)
    (a : Fin n → E) (y : Fin n → ℝ) (v : E) :
    HasGradientAt (smoothedEmpirical r a y) (smoothedEmpiricalGradient r a y v) v := by
  have h := (HasFDerivAt.fun_sum (u := univ) (fun i _ =>
    (smoothedLinearLoss_hasGradient r hr (a i) (y i) v).hasFDerivAt)).const_mul (n : ℝ)⁻¹
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! h using 1
  ext w
  simp [smoothedEmpiricalGradient,InnerProductSpace.toDual_apply_apply,
    inner_sum,inner_smul_left,mul_comm,Finset.mul_sum]
lemma smoothedEmpirical_convex {n : ℕ} (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) :
    ConvexOn ℝ univ (smoothedEmpirical r a y) := by
  refine ⟨convex_univ,?_⟩
  intro v hv w hw c e hc he hce
  unfold smoothedEmpirical
  simp only [smul_eq_mul]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
        (c*smoothedLinearLoss r (a i) (y i) v+e*smoothedLinearLoss r (a i) (y i) w) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro i hi
      exact (smoothedLinearLoss_convex r (a i) (y i)).2 hv hw hc he hce
    _ = _ := by rw [sum_add_distrib,← mul_sum,← mul_sum]; ring
lemma smoothedEmpirical_approx {n : ℕ} (hn : 0 < n) (r T : ℝ) (hr : 0 ≤ r)
    (a : Fin n → E) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : E) :
    linearEmpirical a y v ≤ smoothedEmpirical r a y v ∧
      smoothedEmpirical r a y v ≤ linearEmpirical a y v+r*T := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_le_sum (fun i _ => (smoothedLinearLoss_approx r hr (a i) (y i) v).1)
  · unfold smoothedEmpirical linearEmpirical
    calc
      _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, (absoluteLinearLoss (a i) (y i) v+r*T) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum
        intro i hi
        exact (smoothedLinearLoss_approx r hr (a i) (y i) v).2.trans (by gcongr; exact ha i)
      _ = _ := by rw [sum_add_distrib]; simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
lemma smoothedEmpiricalGradient_lipschitz {n : ℕ} (hn : 0 < n) (r T : ℝ) (hr : 0 < r)
    (a : Fin n → E) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v w : E) :
    ‖smoothedEmpiricalGradient r a y v-smoothedEmpiricalGradient r a y w‖ ≤
      (2*T/r)*‖v-w‖ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold smoothedEmpiricalGradient
  rw [← smul_sub,← sum_sub_distrib,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n,
        ‖smoothedLinearGradient r (a i) (y i) v-smoothedLinearGradient r (a i) (y i) w‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (2*T/r)*‖v-w‖ := by
      gcongr with i
      exact (smoothedLinearGradient_lipschitz r hr (a i) (y i) v w).trans (by gcongr; exact ha i)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
lemma smoothedEmpiricalGradient_norm {n : ℕ} (hn : 0 < n) (T : ℝ)
    (r : ℝ) (a : Fin n → E) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : E) :
    ‖smoothedEmpiricalGradient r a y v‖ ≤ T := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold smoothedEmpiricalGradient
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ‖smoothedLinearGradient r (a i) (y i) v‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, T := by
      gcongr with i
      exact (smoothedLinearGradient_norm r (a i) (y i) v).trans (ha i)
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedRegressionOracle
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
noncomputable def scalarSmoothedSubgradient {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ)
    (v : Vec D) (z : ℝ) : Vec D :=
  thresholdStep 0 (inner ℝ v a-y+r*‖a‖*z) • a
lemma scalarSmoothedSubgradient_measurable {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) :
    Measurable (fun q : Vec D × ℝ => scalarSmoothedSubgradient r a y q.1 q.2) := by
  exact ((thresholdStep_measurable 0).comp (by fun_prop)).smul measurable_const
lemma scalarSmoothedSubgradient_norm {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) (v : Vec D) (z : ℝ) :
    ‖scalarSmoothedSubgradient r a y v z‖ = ‖a‖ := by
  simp only [scalarSmoothedSubgradient,norm_smul,Real.norm_eq_abs,thresholdStep_abs,one_mul]
lemma scalarSmoothedSubgradient_memLp {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) (v : Vec D) :
    MemLp (scalarSmoothedSubgradient r a y v) 2 (gaussianReal 0 1) := by
  apply MemLp.of_bound ((scalarSmoothedSubgradient_measurable r a y).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable ‖a‖
  exact ae_of_all _ (fun z => (scalarSmoothedSubgradient_norm r a y v z).le)
lemma scalarSmoothedSubgradient_mean {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) (v : Vec D) :
    (∫ z, scalarSmoothedSubgradient r a y v z ∂gaussianReal 0 1) =
      smoothedLinearGradient r a y v := by
  unfold scalarSmoothedSubgradient smoothedLinearGradient smoothAbsSlope
  exact integral_smul_const _ _
lemma scalarSmoothedSubgradient_variance {D : ℕ} (r : ℝ) (a : Vec D) (y : ℝ) (v : Vec D) :
    euclideanVariance (gaussianReal 0 1) (scalarSmoothedSubgradient r a y v) ≤ ‖a‖^2 := by
  apply euclideanVariance_le_of_bounded _ _
    ((scalarSmoothedSubgradient_measurable r a y).comp (measurable_const.prodMk measurable_id))
    ‖a‖ (norm_nonneg _)
  exact fun z => (scalarSmoothedSubgradient_norm r a y v z).le
noncomputable def batchSmoothedSubgradient {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (v : Vec D) (z : Fin n → ℝ) : Vec D :=
  (n : ℝ)⁻¹ • ∑ i, scalarSmoothedSubgradient r (a i) (y i) v (z i)
lemma batchSmoothedSubgradient_measurable {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) :
    Measurable (fun q : Vec D × (Fin n → ℝ) => batchSmoothedSubgradient r a y q.1 q.2) := by
  have hi (i : Fin n) : Measurable (fun q : Vec D × (Fin n → ℝ) =>
      scalarSmoothedSubgradient r (a i) (y i) q.1 (q.2 i)) :=
    by
      unfold scalarSmoothedSubgradient
      exact ((thresholdStep_measurable 0).comp (by fun_prop)).smul measurable_const
  have hsum : Measurable (fun q : Vec D × (Fin n → ℝ) =>
      ∑ i, scalarSmoothedSubgradient r (a i) (y i) q.1 (q.2 i)) :=
    Finset.measurable_sum univ (fun i _ => hi i)
  convert! hsum.const_smul (n : ℝ)⁻¹ using 1
lemma batchSmoothedSubgradient_memLp {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    MemLp (batchSmoothedSubgradient r a y v) 2 (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi (i : Fin n) : MemLp (fun z : Fin n → ℝ =>
      scalarSmoothedSubgradient r (a i) (y i) v (z i)) 2 (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    (scalarSmoothedSubgradient_memLp r (a i) (y i) v).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)
  convert! (memLp_finsetSum univ (fun i _ => hi i)).const_smul (n : ℝ)⁻¹ using 1
lemma batchSmoothedSubgradient_mean {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    (∫ z, batchSmoothedSubgradient r a y v z ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
      smoothedEmpiricalGradient r a y v := by
  unfold batchSmoothedSubgradient smoothedEmpiricalGradient
  rw [integral_smul,integral_finsetSum]
  · congr 1
    apply sum_congr rfl
    intro i hi
    have hp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i
    rw [← integral_map hp.measurable.aemeasurable
      (by rw [hp.map_eq]; exact (scalarSmoothedSubgradient_memLp r (a i) (y i) v).aestronglyMeasurable), hp.map_eq,
      scalarSmoothedSubgradient_mean]
  · intro i hi
    exact ((scalarSmoothedSubgradient_memLp r (a i) (y i) v).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i)).integrable (by norm_num)
lemma batchSmoothedSubgradient_variance {D n : ℕ} (hn : 0 < n) (r T : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : Vec D) :
    euclideanVariance (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (batchSmoothedSubgradient r a y v) ≤ T^2/(n : ℝ) := by
  have hv (i : Fin n) : euclideanVariance (gaussianReal 0 1)
      (scalarSmoothedSubgradient r (a i) (y i) v) ≤ T^2 :=
    (scalarSmoothedSubgradient_variance r (a i) (y i) v).trans
      (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2)
  convert! euclideanVariance_average_pi_le hn (fun _ : Fin n => gaussianReal 0 1)
    (fun i => scalarSmoothedSubgradient r (a i) (y i) v)
    (fun i => scalarSmoothedSubgradient_memLp r (a i) (y i) v) (T^2) hv using 1
lemma batchSmoothedSubgradient_norm {D n : ℕ} (hn : 0 < n) (r T : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : Vec D) (z : Fin n → ℝ) :
    ‖batchSmoothedSubgradient r a y v z‖ ≤ T := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold batchSmoothedSubgradient
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, ‖scalarSmoothedSubgradient r (a i) (y i) v (z i)‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, T := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro i hi
      rw [scalarSmoothedSubgradient_norm]
      exact ha i
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.UnivariateGaussianBasis
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_coordinate_map (d : ℕ) (i : Fin d) :
    (gaussian d).map (fun x : Vec d => x i) = gaussianReal 0 1 := by
  rw [gaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (Function.eval i) = _
  exact (measurePreserving_eval (μ := fun _ : Fin d => gaussianReal 0 1) i).map_eq
lemma gaussian_coordinate_preserving (d : ℕ) (i : Fin d) :
    MeasurePreserving (fun x : Vec d => x i) (gaussian d) (gaussianReal 0 1) :=
  ⟨by fun_prop, gaussian_coordinate_map d i⟩
noncomputable def reindexHilbertBasis {ι κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) (e : κ ≃ ι) : HilbertBasis κ ℝ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (fun j => b (e j)) = Set.range b := by
      exact e.surjective.range_comp b
    change ⊤ ≤ (Submodule.span ℝ (Set.range (fun j => b (e j)))).topologicalClosure
    rw [hr, b.dense_span])
lemma reindexHilbertBasis_apply {ι κ E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (b : HilbertBasis ι ℝ E) (e : κ ≃ ι) (j : κ) :
    reindexHilbertBasis b e j = b (e j) := by
  simp only [reindexHilbertBasis, HilbertBasis.coe_mk, Function.comp_apply]
lemma univariate_gaussian_basis :
    ∃ b : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussian 1)),
      ∀ n, (fun x => (b n) x) =ᵐ[gaussian 1]
        (fun x => AMPLowDeg.RankOne.hermNorm n (x 0)) := by
  obtain ⟨b, hb⟩ := (lemma_B_8 1).2.2.1
  let e : ℕ ≃ (Fin 1 → ℕ) := (Equiv.funUnique (Fin 1) ℕ).symm
  refine ⟨reindexHilbertBasis b e, ?_⟩
  intro n
  rw [reindexHilbertBasis_apply]
  convert! hb (e n) using 1
  ext x
  simp [hermite, e, Equiv.funUnique]
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.StandardGaussianMoments
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
lemma gaussian_id_memLp (D : ℕ) : MemLp (fun z : Vec D => z) 2 (gaussian D) := by
  unfold gaussian
  exact IsGaussian.memLp_id (stdGaussian (Vec D)) 2 (by norm_num)
lemma gaussian_id_mean (D : ℕ) : (∫ z : Vec D, z ∂gaussian D) = 0 :=
  integral_id_stdGaussian
lemma gaussian_norm_sq_mean (D : ℕ) : (∫ z : Vec D, ‖z‖^2 ∂gaussian D) = D := by
  have hc (j : Fin D) : MemLp (fun z : Vec D => z j) 2 (gaussian D) :=
    euclidean_coordinate_memLp _ _ (gaussian_id_memLp D) j
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum univ (fun j _ => (hc j).integrable_sq)]
  have he (j : Fin D) : (∫ z : Vec D, (z j)^2 ∂gaussian D) = 1 := by
    have hp := gaussian_coordinate_preserving D j
    have ht : (∫ z : ℝ, z^2 ∂gaussianReal 0 1) = 1 := by
      have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
      rw [variance_eq_integral (by fun_prop)] at h
      simpa [integral_id_gaussianReal] using h
    rw [← hp.map_eq,integral_map hp.measurable.aemeasurable (by fun_prop)] at ht
    exact ht
  simp_rw [he]
  simp
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.NoisyRegressionOracle
open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
local instance (D : ℕ) : IsProbabilityMeasure (gaussian D) := by unfold gaussian; infer_instance
abbrev RegressionNoise (n D : ℕ) := (Fin n → ℝ) × Vec D
noncomputable def regressionNoiseLaw (n D : ℕ) : Measure (RegressionNoise n D) :=
  (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussian D)
instance regressionNoiseLaw_probability (n D : ℕ) : IsProbabilityMeasure (regressionNoiseLaw n D) := by
  unfold regressionNoiseLaw
  infer_instance
noncomputable def noisyRegressionOracle {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ)
    (v : Vec D) (q : RegressionNoise n D) : Vec D :=
  batchSmoothedSubgradient r a y v q.1 + τ • q.2
lemma noisyRegressionOracle_measurable {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) :
    Measurable (Function.uncurry (noisyRegressionOracle r τ a y)) := by
  have hbatch : Measurable (fun q : Vec D × RegressionNoise n D =>
      batchSmoothedSubgradient r a y q.1 q.2.1) := by
    convert! (batchSmoothedSubgradient_measurable r a y).comp
      (measurable_fst.prodMk measurable_snd.fst) using 1
  exact hbatch.add (measurable_snd.snd.const_smul τ)
lemma noisyRegressionOracle_memLp {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    MemLp (noisyRegressionOracle r τ a y v) 2 (regressionNoiseLaw n D) := by
  have hbatch := (batchSmoothedSubgradient_memLp r a y v).comp_fst (gaussian D)
  have hgauss := (gaussian_id_memLp D).comp_snd (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
  convert! hbatch.add (hgauss.const_smul τ) using 1
lemma noisyRegressionOracle_mean {D n : ℕ} (r τ : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    (∫ q, noisyRegressionOracle r τ a y v q ∂regressionNoiseLaw n D) =
      smoothedEmpiricalGradient r a y v := by
  have hb := (batchSmoothedSubgradient_memLp r a y v).integrable (by norm_num)
  have hg := (gaussian_id_memLp D).integrable (by norm_num)
  have hgp : Integrable (fun q : RegressionNoise n D => τ • q.2) (regressionNoiseLaw n D) := by
    convert! (hg.comp_snd (Measure.pi (fun _ : Fin n => gaussianReal 0 1))).smul τ using 1
  unfold noisyRegressionOracle regressionNoiseLaw
  rw [integral_add (f := fun q : RegressionNoise n D => batchSmoothedSubgradient r a y v q.1)
    (g := fun q => τ • q.2) (hb.comp_fst _) hgp]
  rw [integral_prod _ (hb.comp_fst _),integral_prod _ hgp]
  simp only [integral_const,probReal_univ,one_smul,batchSmoothedSubgradient_mean]
  have hzero : (∫ z : Vec D, τ • z ∂gaussian D) = 0 := by
    calc
      _ = τ • (∫ z : Vec D, z ∂gaussian D) := by
        convert! integral_smul τ (fun z : Vec D => z) (μ := gaussian D) using 1
      _ = 0 := by rw [gaussian_id_mean,smul_zero]
  rw [hzero,add_zero]
lemma noisyRegressionOracle_variance {D n : ℕ} (hn : 0 < n) (r τ T : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : Vec D) :
    (∫ q, ‖noisyRegressionOracle r τ a y v q-smoothedEmpiricalGradient r a y v‖^2
      ∂regressionNoiseLaw n D) ≤ 2*T^2/(n : ℝ)+2*τ^2*D := by
  let g := smoothedEmpiricalGradient r a y v
  have hb := (batchSmoothedSubgradient_memLp r a y v).sub (memLp_const g)
  have hbi : Integrable (fun z => ‖batchSmoothedSubgradient r a y v z-g‖^2)
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
    convert! (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb using 1
  have hg : Integrable (fun z : Vec D => ‖z‖^2) (gaussian D) :=
    (memLp_two_iff_integrable_sq_norm (gaussian_id_memLp D).aestronglyMeasurable).mp (gaussian_id_memLp D)
  have he := (noisyRegressionOracle_memLp r τ a y v).sub (memLp_const g)
  have hei : Integrable (fun q => ‖noisyRegressionOracle r τ a y v q-g‖^2)
      (regressionNoiseLaw n D) := by
    convert! (memLp_two_iff_integrable_sq_norm he.aestronglyMeasurable).mp he using 1
  have hri : Integrable (fun q : RegressionNoise n D =>
      2*‖batchSmoothedSubgradient r a y v q.1-g‖^2+2*τ^2*‖q.2‖^2) (regressionNoiseLaw n D) :=
    ((hbi.comp_fst _).const_mul 2).add ((hg.comp_snd _).const_mul (2*τ^2))
  have hpoint (q : RegressionNoise n D) :
      ‖noisyRegressionOracle r τ a y v q-g‖^2 ≤
        2*‖batchSmoothedSubgradient r a y v q.1-g‖^2+2*τ^2*‖q.2‖^2 := by
    have hsum := norm_add_le (batchSmoothedSubgradient r a y v q.1-g) (τ • q.2)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hsum 2
    have hs2 := sq_nonneg (‖batchSmoothedSubgradient r a y v q.1-g‖-‖τ • q.2‖)
    have heq : noisyRegressionOracle r τ a y v q-g =
        (batchSmoothedSubgradient r a y v q.1-g)+τ • q.2 := by
      unfold noisyRegressionOracle
      abel
    rw [heq]
    have hnorm : ‖batchSmoothedSubgradient r a y v q.1-g+τ • q.2‖^2 ≤
        2*‖batchSmoothedSubgradient r a y v q.1-g‖^2+2*‖τ • q.2‖^2 := by nlinarith
    simpa only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc] using hnorm
  have hm := integral_mono hei hri hpoint
  have hR : (∫ q : RegressionNoise n D,
      2*‖batchSmoothedSubgradient r a y v q.1-g‖^2+2*τ^2*‖q.2‖^2 ∂regressionNoiseLaw n D) =
      2*euclideanVariance (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
        (batchSmoothedSubgradient r a y v) + 2*τ^2*D := by
    unfold regressionNoiseLaw
    rw [integral_add ((hbi.comp_fst _).const_mul 2) ((hg.comp_snd _).const_mul (2*τ^2)),
      integral_const_mul,integral_const_mul,
      integral_prod _ (hbi.comp_fst _),integral_prod _ (hg.comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul,gaussian_norm_sq_mean]
    rw [euclideanVariance,batchSmoothedSubgradient_mean]
  rw [hR] at hm
  have hv := mul_le_mul_of_nonneg_left (batchSmoothedSubgradient_variance hn r T a y ha v)
    (by norm_num : (0 : ℝ) ≤ 2)
  exact hm.trans (by simpa only [mul_div_assoc] using add_le_add_left hv (2*τ^2*D))
lemma noisyRegressionOracle_bound {D n : ℕ} (hn : 0 < n) (r τ T : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (v : Vec D) (q : RegressionNoise n D) :
    ‖noisyRegressionOracle r τ a y v q‖ ≤ T+|τ| *‖q.2‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (batchSmoothedSubgradient_norm hn r T a y ha v q.1) (by simp [norm_smul]))
lemma noisyRegressionOracle_envelope_memLp (n D : ℕ) (τ T : ℝ) :
    MemLp (fun q : RegressionNoise n D => T+|τ| *‖q.2‖) 2 (regressionNoiseLaw n D) := by
  have hg := (gaussian_id_memLp D).norm.comp_snd (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
  convert! (memLp_const T).add (hg.const_smul |τ|) using 1
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.SmoothedEmpiricalProperties
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
lemma smoothedEmpirical_continuous {D n : ℕ} (r : ℝ) (hr : 0 < r)
    (a : Fin n → Vec D) (y : Fin n → ℝ) : Continuous (smoothedEmpirical r a y) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (smoothedEmpirical_hasGradient r hr a y v).differentiableAt.continuousAt
lemma smoothedEmpiricalGradient_continuous {D n : ℕ} (hn : 0 < n) (r T : ℝ) (hr : 0 < r)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) :
    Continuous (smoothedEmpiricalGradient r a y) := by
  have hT : 0 ≤ T := (norm_nonneg (a ⟨0,hn⟩)).trans (ha _)
  have hk : 0 ≤ 2*T/r := by positivity
  apply LipschitzWith.continuous (K := (2*T/r).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm,Real.coe_toNNReal _ hk]
  exact smoothedEmpiricalGradient_lipschitz hn r T hr a y ha v w
lemma smoothedEmpirical_nonneg {D n : ℕ} (r : ℝ) (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    0 ≤ smoothedEmpirical r a y v := by
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro i hi
  exact integral_nonneg (fun z => abs_nonneg _)
lemma linearEmpirical_bound {D n : ℕ} (hn : 0 < n) (T Y : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (v : Vec D) (hv : ‖v‖ ≤ 1) : linearEmpirical a y v ≤ T+Y := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold linearEmpirical
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (T+Y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum
      intro i hi
      change |inner ℝ v (a i)-y i| ≤ T+Y
      calc
        _ ≤ |inner ℝ v (a i)|+|y i| := abs_sub _ _
        _ ≤ ‖v‖*‖a i‖+Y := add_le_add (by simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) v (a i))) (hy i)
        _ ≤ T+Y := by nlinarith [norm_nonneg v,norm_nonneg (a i),ha i]
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
lemma smoothedEmpirical_bound {D n : ℕ} (hn : 0 < n) (r T Y : ℝ) (hr : 0 ≤ r)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (v : Vec D) (hv : ‖v‖ ≤ 1) : |smoothedEmpirical r a y v| ≤ T+Y+r*T := by
  rw [abs_of_nonneg (smoothedEmpirical_nonneg r a y v)]
  exact (smoothedEmpirical_approx hn r T hr a y ha v).2.trans
    (add_le_add (linearEmpirical_bound hn T Y a y ha hy v hv) le_rfl)
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.AcceleratedStepsizeBound
open Finset
open scoped BigOperators
set_option autoImplicit false
namespace PrivateAgnosticHalfspace.Gaussian
noncomputable def regressionStepsize (L σ : ℝ) (N : ℕ) : ℝ :=
  min (1/(2*L)) (1/(σ*N*Real.sqrt N))
lemma regressionStepsize_pos (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    0 < regressionStepsize L σ N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold regressionStepsize
  apply lt_min <;> positivity
lemma regressionStepsize_smooth (L σ : ℝ) (hL : 0 < L) (N : ℕ) :
    L*regressionStepsize L σ N ≤ 1/2 := by
  have h := mul_le_mul_of_nonneg_left (min_le_left (1/(2*L)) (1/(σ*N*Real.sqrt N))) hL.le
  have he : L*(1/(2*L)) = 1/2 := by field_simp <;> ring
  exact he ▸ h
lemma regressionStepsize_inv_bound (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    (regressionStepsize L σ N)⁻¹ ≤ 2*L+σ*N*Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  unfold regressionStepsize
  rcases le_total (1/(2*L)) (1/(σ*N*Real.sqrt N)) with h|h
  · rw [min_eq_left h,one_div,inv_inv]
    nlinarith [show 0 ≤ σ*(N : ℝ)*Real.sqrt N by positivity]
  · rw [min_eq_right h,one_div,inv_inv]
    linarith
lemma accelerated_stepsize_error_bound (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ)
    (N : ℕ) (hN : 1 ≤ N) (R2 : ℝ) (hR : 0 ≤ R2 ∧ R2 ≤ 1) :
    NonconvexAG.Smooth.Gamma accelAlpha N * (R2/regressionStepsize L σ N) +
      3*σ^2*regressionStepsize L σ N*N ≤ 4*L/(N : ℝ)^2+5*σ/Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hβ := regressionStepsize_pos L σ hL hσ N hN
  have hG := accelGamma_pos N hN
  have hΓ : NonconvexAG.Smooth.Gamma accelAlpha N ≤ 2/(N : ℝ)^2 := by
    rw [accelGamma_formula N hN]
    apply (div_le_div_iff₀ (by positivity : 0 < (N : ℝ)*((N : ℝ)+1)) (by positivity : 0 < (N : ℝ)^2)).mpr
    nlinarith
  have hfirst : NonconvexAG.Smooth.Gamma accelAlpha N*(R2/regressionStepsize L σ N) ≤
      4*L/(N : ℝ)^2+2*σ/Real.sqrt N := by
    calc
      _ ≤ (2/(N : ℝ)^2)*(1/regressionStepsize L σ N) := by
        apply mul_le_mul hΓ _ (div_nonneg hR.1 hβ.le) (by positivity)
        exact div_le_div_of_nonneg_right hR.2 hβ.le
      _ ≤ (2/(N : ℝ)^2)*(2*L+σ*N*Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [one_div] using regressionStepsize_inv_bound L σ hL hσ N hN
      _ = _ := by
        have hsq := Real.sq_sqrt hn.le
        field_simp
        nlinarith [congrArg (fun x : ℝ => 2*(N : ℝ)*σ*x) hsq]
  have hsecond : 3*σ^2*regressionStepsize L σ N*N ≤ 3*σ/Real.sqrt N := by
    calc
      _ ≤ 3*σ^2*(1/(σ*N*Real.sqrt N))*N := by
        gcongr
        exact min_le_right _ _
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ (4*L/(N : ℝ)^2+2*σ/Real.sqrt N)+(3*σ/Real.sqrt N) := add_le_add hfirst hsecond
    _ = _ := by ring
end PrivateAgnosticHalfspace.Gaussian
end

section
-- Solutions.SmoothedRegressionOptimization
open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
open NonconvexAG.StochComposite
lemma linearEmpirical_continuous {D n : ℕ} (a : Fin n → Vec D) (y : Fin n → ℝ) :
    Continuous (linearEmpirical a y) := by
  unfold linearEmpirical absoluteLinearLoss
  apply Continuous.const_mul
  exact continuous_finsetSum _ (fun i _ => by fun_prop)
lemma linearEmpirical_nonneg {D n : ℕ} (a : Fin n → Vec D) (y : Fin n → ℝ) (v : Vec D) :
    0 ≤ linearEmpirical a y v := mul_nonneg (by positivity) (sum_nonneg (fun i _ => abs_nonneg _))
noncomputable def regressionVectorOutput {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ)
    (s : Fin (n+1) → RegressionNoise n D) : Vec D :=
  xagSeq (noisyRegressionOracle r τ a y) (fun x z c => unitProjection (x-c • z))
    accelAlpha (fun _ => β) (accelLambda β) (fun _ => 1) 0
    (fun k s => finiteNoiseSequence (0,0) s k) n s
lemma regressionVectorOutput_norm {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (s : Fin (n+1) → RegressionNoise n D) :
    ‖regressionVectorOutput r τ β a y s‖ ≤ 1 := by
  have h := rsagPath_projected_mem (noisyRegressionOracle r τ a y) (Metric.closedBall 0 1) unitProjection
    (fun x => (unitProjection_isProjection D x).1) accelAlpha (fun _ => β) (accelLambda β) 0 (by simp)
    (finiteNoiseSequence (0,0) s) n
  simpa only [Metric.mem_closedBall,dist_zero_right,regressionVectorOutput,xagSeq] using h.2
lemma regressionVectorOutput_measurable {D n : ℕ} (r τ β : ℝ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) : Measurable (regressionVectorOutput r τ β a y) := by
  have hP : Measurable (fun q : (Vec D × Vec D) × ℝ => unitProjection (q.1.1-q.2 • q.1.2)) :=
    (unitProjection_continuous D).measurable.comp (by fun_prop)
  have h := rsagPath_one_measurable (noisyRegressionOracle r τ a y) (noisyRegressionOracle_measurable r τ a y)
    (fun x z c => unitProjection (x-c • z)) hP accelAlpha (fun _ => β) (accelLambda β) 0
    (fun k (s : Fin (n+1) → RegressionNoise n D) => finiteNoiseSequence (0,0) s k)
    (fun k => finiteNoiseSequence_measurable (N := n) (0,0) k) n
  exact h.snd
lemma regressionVectorOutput_expected {D n : ℕ} (hn : 0 < n) (r τ T Y σ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hσ : 0 < σ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (hσbound : 2*T^2/(n : ℝ)+2*τ^2*D ≤ σ^2) (vstar : Vec D) (hvstar : ‖vstar‖ ≤ 1) :
    let L := 2*T/r
    let β := regressionStepsize L σ n
    let out := regressionVectorOutput r τ β a y
    let ν := Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)
    Integrable (fun s => linearEmpirical a y (out s)-linearEmpirical a y vstar) ν ∧
      (∫ s, linearEmpirical a y (out s)-linearEmpirical a y vstar ∂ν) ≤
        r*T+4*L/(n : ℝ)^2+5*σ/Real.sqrt n := by
  let F := smoothedEmpirical r a y
  let g := smoothedEmpiricalGradient r a y
  let L := 2*T/r
  let β := regressionStepsize L σ n
  let out := regressionVectorOutput r τ β a y
  let ν := Measure.pi (fun _ : Fin (n+1) => regressionNoiseLaw n D)
  have hL : 0 < L := by dsimp [L]; positivity
  have hβ := regressionStepsize_pos L σ hL hσ n hn
  have hLβ := regressionStepsize_smooth L σ hL n
  have hFcont := smoothedEmpirical_continuous r hr a y
  have hgcont := smoothedEmpiricalGradient_continuous hn r T hr a y ha
  have hsmooth : ConvexOptAlg.SmoothGD.IsBetaSmooth F g L :=
    ⟨hL.le,smoothedEmpirical_hasGradient r hr a y,smoothedEmpiricalGradient_lipschitz hn r T hr a y ha⟩
  have hi := finite_projected_optimizer_utility (Nat.one_le_iff_ne_zero.mpr hn.ne')
    (regressionNoiseLaw n D) (0,0) F g L hsmooth (smoothedEmpirical_convex r a y)
    hFcont.measurable hgcont.measurable (T+Y+r*T) T
    (smoothedEmpirical_bound hn r T Y hr.le a y ha hy)
    (smoothedEmpiricalGradient_norm hn T r a y ha)
    (noisyRegressionOracle r τ a y) (noisyRegressionOracle_measurable r τ a y)
    (fun q : RegressionNoise n D => T+|τ| * ‖q.2‖) (noisyRegressionOracle_envelope_memLp n D τ T)
    (noisyRegressionOracle_bound hn r τ T a y ha) (noisyRegressionOracle_mean r τ a y)
    σ β (fun v => (noisyRegressionOracle_variance hn r τ T a y ha v).trans hσbound)
    hβ hLβ vstar hvstar
  have hlin : Integrable (fun s => linearEmpirical a y (out s)-linearEmpirical a y vstar) ν := by
    apply (integrable_const (T+Y+|linearEmpirical a y vstar|)).mono'
      (((linearEmpirical_continuous a y).measurable.comp (regressionVectorOutput_measurable r τ β a y)).sub
        measurable_const).aestronglyMeasurable
    apply ae_of_all
    intro s
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |linearEmpirical a y (out s)|+|linearEmpirical a y vstar| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_of_nonneg (linearEmpirical_nonneg a y _)]
        exact add_le_add (linearEmpirical_bound hn T Y a y ha hy _ (regressionVectorOutput_norm r τ β a y s)) le_rfl
  have hpoint (s) : linearEmpirical a y (out s)-linearEmpirical a y vstar ≤ F (out s)-F vstar+r*T := by
    have h1 := (smoothedEmpirical_approx hn r T hr.le a y ha (out s)).1
    have h2 := (smoothedEmpirical_approx hn r T hr.le a y ha vstar).2
    linarith
  have hfi : Integrable (fun s => F (out s)-F vstar) ν := hi.1
  have hright : Integrable (fun s => F (out s)-F vstar+r*T) ν := by
    convert! hfi.add (integrable_const (r*T)) using 1
  have hm := integral_mono hlin hright hpoint
  rw [integral_add (f := fun s => F (out s)-F vstar) (g := fun _ => r*T) hfi
    (integrable_const (r*T)),integral_const,probReal_univ,one_smul] at hm
  have hrange : 0 ≤ ‖vstar‖^2 ∧ ‖vstar‖^2 ≤ 1 := ⟨sq_nonneg _,by nlinarith [norm_nonneg vstar]⟩
  have hrate := accelerated_stepsize_error_bound L σ hL hσ n (Nat.one_le_iff_ne_zero.mpr hn.ne') (‖vstar‖^2) hrange
  have hstat : (∫ s, F (out s)-F vstar ∂ν) ≤
      NonconvexAG.Smooth.Gamma accelAlpha n*(‖vstar‖^2/β)+3*σ^2*β*n := hi.2
  refine ⟨hlin,?_⟩
  change (∫ s, linearEmpirical a y (out s)-linearEmpirical a y vstar ∂ν) ≤ r*T+4*L/(n : ℝ)^2+5*σ/Real.sqrt n
  calc
    _ ≤ (∫ s, F (out s)-F vstar ∂ν)+r*T := hm
    _ ≤ (NonconvexAG.Smooth.Gamma accelAlpha n*(‖vstar‖^2/β)+3*σ^2*β*n)+r*T := add_le_add hstat le_rfl
    _ ≤ (4*L/(n : ℝ)^2+5*σ/Real.sqrt n)+r*T := add_le_add hrate le_rfl
    _ = _ := by ring
end PrivateAgnosticHalfspace.Gaussian.RegressionGeometry
end

section
-- Solutions.Sol_projected_regression_expected_error
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open PrivateAgnosticHalfspace.Gaussian
set_option autoImplicit false

open PrivateAgnosticHalfspace.Gaussian.RegressionGeometry

theorem solution {D n : ℕ} (hn : 0 < n) (r τ T Y σ : ℝ)
    (hr : 0 < r) (hT : 0 < T) (hσ : 0 < σ)
    (a : Fin n → Vec D) (y : Fin n → ℝ) (ha : ∀ i, ‖a i‖ ≤ T) (hy : ∀ i, |y i| ≤ Y)
    (hσbound : 2*T^2/(n : ℝ)+2*τ^2*D ≤ σ^2) (vstar : Vec D) (hvstar : ‖vstar‖ ≤ 1) :
    let L := 2*T/r
    let β := min (1/(2*L)) (1/(σ*n*Real.sqrt n))
    let Ξ := (Fin n → ℝ) × Vec D
    let G := fun (v : Vec D) (q : Ξ) =>
      (n : ℝ)⁻¹ • (∑ i, (if 0 ≤ inner ℝ v (a i)-y i+r*‖a i‖*q.1 i then (1 : ℝ) else -1) • a i) + τ • q.2
    let out := NonconvexAG.StochComposite.xagSeq G
      (fun x z c => (max 1 ‖x-c • z‖)⁻¹ • (x-c • z))
      (fun k => 2/((k : ℝ)+1)) (fun _ => β) (fun k => (k : ℝ)*β/2) (fun _ => 1) 0
      (fun k (s : Fin (n+1) → Ξ) => if hk : k < n+1 then s ⟨k,hk⟩ else (0,0)) n
    let ν := Measure.pi (fun _ : Fin (n+1) =>
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussian D))
    let F := fun v : Vec D => (n : ℝ)⁻¹ * ∑ i, |inner ℝ v (a i)-y i|
    Integrable (fun s => F (out s)-F vstar) ν ∧
      (∫ s, F (out s)-F vstar ∂ν) ≤ r*T+4*L/(n : ℝ)^2+5*σ/Real.sqrt n
 := by
  exact regressionVectorOutput_expected hn r τ T Y σ hr hT hσ a y ha hy hσbound vstar hvstar
end
