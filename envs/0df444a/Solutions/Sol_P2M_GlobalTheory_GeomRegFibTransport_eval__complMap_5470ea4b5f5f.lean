-- Prove2me | solution 1 for P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:53.576317+00:00
-- url     : https://prove2.me/submissions/0675c66e-3511-4b82-84cb-ed8fb64f2643

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems
namespace GlobalTheory.GeomRegFibTransport
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap e I J h x) =
      Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)
        (AdicCompletion.evalₐ I n x) := by
  unfold complMap
  exact AdicCompletion.evalₐ_liftRingHom J _ (complMap_compat e I J h) n x
end GlobalTheory.GeomRegFibTransport
