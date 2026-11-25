-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.fromSpec_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:32.441715+00:00
-- url     : https://prove2.me/submissions/54a12ca4-a9d1-455d-a8d1-f5ceb0e1db35

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
section Br
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}
private lemma fromSpec_specializes_iff_le {V : W.Opens} (hV : IsAffineOpen V) (P Q : PrimeSpectrum Γ(W, V)) :
    hV.fromSpec P ⤳ hV.fromSpec Q ↔ P ≤ Q := by
  exact hV.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.trans
    (PrimeSpectrum.le_iff_specializes P Q).symm
end Br
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (hq : ParPrimes hU hy f q) (i : Fin n) : hU.fromSpec (q i) ⤳ y := by
  have h := (fromSpec_specializes_iff_le hU (q i) (hU.primeIdealOf ⟨y, hy⟩)).2 (hq.1 i)
  rwa [hU.fromSpec_primeIdealOf] at h
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
