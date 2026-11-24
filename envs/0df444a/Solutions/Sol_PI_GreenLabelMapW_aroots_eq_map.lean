-- Prove2me | solution 1 for PI.GreenLabelMapW.aroots_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:33.061664+00:00
-- url     : https://prove2.me/submissions/5d24d9bf-f0e4-4e75-8434-336f13b9cf5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Theorems.Thm_PI_GreenLabelMapW_conj_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IntermediateField
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K]
namespace PI.GreenLabelMapW
theorem _root_.solution {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).aroots (AlgebraicClosure K) = (P.aroots (AlgebraicClosure K)).map f := by
  have hsep : P.Separable := PerfectField.separable_of_irreducible hi
  have hint : IsIntegral K (f w) := Algebra.IsIntegral.isIntegral _
  have hsep2 : (minpoly K (f w)).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hP0 : P ≠ 0 := hm.ne_zero
  have hnd1 : ((minpoly K (f w)).aroots (AlgebraicClosure K)).Nodup :=
    (Polynomial.nodup_aroots_iff_of_splits (minpoly.ne_zero hint) (IsAlgClosed.splits _)).2 hsep2
  have hnd2 : (P.aroots (AlgebraicClosure K)).Nodup :=
    (Polynomial.nodup_aroots_iff_of_splits hP0 (IsAlgClosed.splits _)).2 hsep
  have hnd3 : ((P.aroots (AlgebraicClosure K)).map f).Nodup :=
    Multiset.Nodup.map_on (fun r₁ h₁ r₂ h₂ h =>
      hinj r₁ r₂ (Polynomial.mem_aroots.1 h₁).2 (Polynomial.mem_aroots.1 h₂).2 h) hnd2
  refine (Multiset.Nodup.ext hnd1 hnd3).2 fun y => ?_
  rw [Polynomial.mem_aroots, Multiset.mem_map]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨r, hr, hry⟩ := (conj_roots hm hi hw f hf y).1 hy
    exact ⟨r, Polynomial.mem_aroots.2 ⟨hP0, hr⟩, hry⟩
  · rintro ⟨r, hr, hry⟩
    exact ⟨minpoly.ne_zero hint, (conj_roots hm hi hw f hf y).2 ⟨r, (Polynomial.mem_aroots.1 hr).2, hry⟩⟩
end PI.GreenLabelMapW
