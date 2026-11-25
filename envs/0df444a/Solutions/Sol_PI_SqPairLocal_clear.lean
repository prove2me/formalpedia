-- Prove2me | solution 1 for PI.SqPairLocal.clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:49.675974+00:00
-- url     : https://prove2.me/submissions/6fd45db5-7c63-4b56-a613-dfe181ccd051

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_DivAtOneOfInt
import Theorems.Thm_PI_SqPairLocal_one_nmem
import Theorems.Thm_PI_SqPairLocal_mul_nmem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution {L : Submodule (𝓞 E) (Fin N → E)} (hL : L.FG) {M : Matrix (Fin N) (Fin N) E}
    (h : ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ s • (M *ᵥ y) ∈ L) :
    ∃ s : 𝓞 E, s ∉ Q ∧ ∀ y ∈ L, s • (M *ᵥ y) ∈ L := by
  classical
  obtain ⟨S, hS⟩ := hL
  choose! t ht using h
  have hSL : ∀ g ∈ S, g ∈ L := fun g hg => hS ▸ Submodule.subset_span (Finset.mem_coe.mpr hg)
  refine ⟨∏ g ∈ S, t g, Finset.prod_induction t (· ∉ Q) (fun a b ha hb => mul_nmem ha hb) one_nmem
    (fun g hg => (ht g (hSL g hg)).1), ?_⟩
  let F : (Fin N → E) →ₗ[𝓞 E] (Fin N → E) :=
    (∏ g ∈ S, t g) • (Matrix.mulVecLin M).restrictScalars (𝓞 E)
  have hle : Submodule.span (𝓞 E) (S : Set (Fin N → E)) ≤ L.comap F := by
    rw [Submodule.span_le]
    intro g hg
    have hg' : g ∈ S := Finset.mem_coe.mp hg
    show (∏ g ∈ S, t g) • (M *ᵥ g) ∈ L
    rw [← Finset.mul_prod_erase S t hg', mul_comm, mul_smul]
    exact L.smul_mem _ (ht g (hSL g hg')).2
  intro y hy
  rw [← hS] at hy
  exact hle hy
end PI.SqPairLocal
