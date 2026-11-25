-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.exists_jacobian_minor_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:06.042876+00:00
-- url     : https://prove2.me/submissions/482dd60a-dc76-43ea-89e3-3a50f5247997

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_GenSmooth
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_exists_jacobian_minor_not_mem__658f34d01f6a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ ℚ) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 :=
  exists_jacobian_minor_not_mem' 𝔭 G hG d hd
end ReciprocityTheory.AnForm.R
