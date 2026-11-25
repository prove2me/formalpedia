-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.val_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:02.361238+00:00
-- url     : https://prove2.me/submissions/896c8724-b9df-4772-bf79-5935ab8f0686

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_reduction_eq_zero_of_integral_inv_mul
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_sum__70ca31df943b
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ent_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gm_int
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_mul__93b5aa3ac6e4
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}
variable (P)
variable {P}
variable {q k₀ r c' n' c n kj : ℕ} (hqq : q = qOf P) (h1 : r = kj + c) (h2 : k₀ ≤ kj) (h3 : kj ≤ n)
  (h4 : r ≤ n' + c') (h5 : k₀ ≤ n')
include hqq h1 h2 h3 h4 h5
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (hp : (Ideal.absNorm P.asIdeal).Prime) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ JQ P q kj n c)
    {y : HomE E (n' + c') (n + c)} (hy : CondQ P q k₀ r c' n' c n y) :
    (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).map (redP P) =
      (GA k₀ r c n g).map (redP P) * (AYm q k₀ r c' n' c n y).map (redP P) := by
  subst hqq
  obtain ⟨hyA, hyB⟩ := hy
  ext s t
  have hs : s.1 < n + c := by have := s.isLt; omega
  have ht : t.1 < n' + c' := by have := t.isLt; omega
  simp only [Matrix.map_apply, Matrix.mul_apply, AYm, GA, Matrix.of_apply]
  rw [ent_comp rfl h1 h2 h3 h4 h5 g y s.1 t.1 hs,
    reduction_sum' _ _ (fun p'' hp'' => ia_mul (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs)
      (hyA p'' t.1 (Finset.mem_range.mp hp'') ht)),
    ← Finset.sum_range_add_sum_Ico _ (show r ≤ n + c by omega)]
  have hzero : ∑ p'' ∈ Finset.Ico r (n + c), redP P (atN (g (eN E (n + c) (fIdx k₀ c n p''))) (fIdx k₀ c n s.1) *
      entB (qOf P) k₀ c' n' c n 0 0 y p'' t.1) = 0 := by
    refine Finset.sum_eq_zero (fun p'' hp'' => ?_)
    obtain ⟨h6, h7⟩ := Finset.mem_Ico.mp hp''
    rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 p'' hs) (hyA p'' t.1 h7 ht),
      reduction_eq_zero_of_integral_inv_mul hp (hyB p'' t.1 h6 h7 t.isLt), mul_zero]
  rw [hzero, add_zero, Finset.sum_range]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [reduction_mul' (P := P) (gm_int rfl h1 h2 h3 h4 h5 hg s.1 x.1 hs) (hyA x.1 t.1 (by have := x.isLt; omega) ht)]
end PI.TwistedEisensteinNonvanishing.W
