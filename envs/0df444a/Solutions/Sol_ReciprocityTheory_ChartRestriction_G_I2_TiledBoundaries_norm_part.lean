-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries.norm_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:20:18.294948+00:00
-- url     : https://prove2.me/submissions/54568e2b-abcd-4940-9367-3eb380420fd4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_NstatementOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_key
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_continuous_pointNormSq_quotient
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_pointwiseNormSq_pullback_tensor_eq_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_add_period
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pointwiseNormSq_translate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pullbackSection_mem_thetaSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
private theorem continuous_of_mem_Sec (X : PT E) {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Continuous F :=
  hF.1.continuous
private theorem continuous_s0_of_continuous (X : PT E) {n : ℕ} (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : Continuous s) : Continuous (s0 X (n := n) π s) := by
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  show Continuous (fun v : Fin n → Vsp X.dim => ∏ k, s fun _ => π (v k))
  exact continuous_finset_prod _ fun k _ =>
    hs.comp (continuous_pi fun _ => hπc.comp (continuous_apply k))
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
theorem _root_.solution (hT : StepT) (hF : StepF) (hP : StepP) (X : PT E) {q n : ℕ}
    {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) (b : Fin n → Vsp X.dim) :
    X.l2 q (X.U q b (s0 X π s)) = X.l2 1 s ^ n := by
  have hπc : Continuous π := LinearMap.continuous_of_finiteDimensional π
  have hsc : Continuous s := continuous_of_mem_Sec X hs
  have hF0 : s0 X (n := n) π s ∈ X.Sec q n := pullbackSection_mem_thetaSpace (X := X) hπ hs
  have hgc : Continuous (X.ptN2 q (s0 X (n := n) π s)) := continuous_pointNormSq_quotient X q (continuous_s0_of_continuous X π hsc)
  have hc1 : Continuous (X.ptN2 1 s) := continuous_pointNormSq_quotient X 1 hsc
  have hgc1 : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => w)) :=
    hc1.comp (continuous_pi fun _ => continuous_id)
  have hfc : Continuous (fun w : Vsp X.dim => X.ptN2 1 s (fun _ => π w)) := hgc1.comp hπc
  have hper : ∀ γ ∈ X.L, ∀ v : Vsp X.dim, X.ptN2 1 s (fun _ => v + γ) = X.ptN2 1 s (fun _ => v) :=
    fun γ hγ v => pointwiseNormSq_add_period (X := X) hs (γ := fun _ => γ) (fun _ => hγ) (fun _ => v)
  have e1 : X.l2 q (X.U q b (s0 X π s)) = ⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v := by
    have key : (⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) (v - b)) =
        ⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v :=
      hT E X n ℝ (X.ptN2 q (s0 X (n := n) π s)) hgc
        (fun γ hγ v => pointwiseNormSq_add_period (X := X) hF0 hγ v) b
    unfold PT.l2
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact pointwiseNormSq_translate (X := X) q b _ v
  have e2 : (⨍ v in X.fd n, X.ptN2 q (s0 X (n := n) π s) v) =
      (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n := by
    have key : (⨍ v in X.fd n, ∏ k, X.ptN2 1 s (fun _ => π (v k))) =
        (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) ^ n :=
      hF E X n (fun w => X.ptN2 1 s (fun _ => π w)) hfc
    refine Eq.trans ?_ key
    congr 1
    funext v
    exact pointwiseNormSq_pullback_tensor_eq_prod X hπ s v
  have e3 : (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => π w)) =
      ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w) :=
    hP E X q π hq hπ (fun w => X.ptN2 1 s (fun _ => w)) hgc1 hper
  have e4 : X.l2 1 s = ⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w) := by
    have key : (⨍ v in X.fd 1, ∏ k, X.ptN2 1 s (fun _ => v k)) =
        (⨍ w in ZSpan.fundamentalDomain X.b, X.ptN2 1 s (fun _ => w)) ^ 1 :=
      hF E X 1 (fun w => X.ptN2 1 s (fun _ => w)) hgc1
    refine Eq.trans ?_ (key.trans (pow_one _))
    unfold PT.l2
    congr 1
    funext v
    rw [Fin.prod_univ_one]
    exact congrArg (X.ptN2 1 s) (funext fun i => congrArg v (Subsingleton.elim i 0))
  rw [e1, e2, e3, e4]
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
