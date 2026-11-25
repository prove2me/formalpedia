-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.det_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:57:02.504705+00:00
-- url     : https://prove2.me/submissions/85365ae8-86c0-483f-a2dc-d381c5bee84d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IsUnitRedP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_JacobianTransformationLaw
import Theorems.Thm_P2M_PI_TwistedEisensteinNonvanishing_W_reduction_det__f5782d4076ff
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gm_int
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_supp_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_val_comp

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
    redP P (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y)).det =
      redP P (GA k₀ r c n g).det * redP P (AYm q k₀ r c' n' c n y).det := by
  have hgy := supp_comp hqq h1 h2 h3 h4 h5 hg hy
  rw [reduction_det' (AYm q k₀ r c' n' c n (g.toLinearMap ∘ₗ y))
      (fun s t => hgy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega)),
    val_comp hqq h1 h2 h3 h4 h5 hp hg hy, Matrix.det_mul,
    reduction_det' (GA k₀ r c n g) (fun s t => gm_int hqq h1 h2 h3 h4 h5 hg s.1 t.1 (by have := s.isLt; omega)),
    reduction_det' (AYm q k₀ r c' n' c n y)
      (fun s t => hy.1 s.1 t.1 (by have := s.isLt; omega) (by have := t.isLt; omega))]
end PI.TwistedEisensteinNonvanishing.W
