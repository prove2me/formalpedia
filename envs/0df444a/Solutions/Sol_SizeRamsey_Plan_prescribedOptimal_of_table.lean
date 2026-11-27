-- Prove2me | solution 1 for SizeRamsey.Plan.prescribedOptimal_of_table
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:27:04.674909+00:00
-- url     : https://prove2.me/submissions/bdd60c8c-9579-4329-98e9-6483727ee896

module
public import Definitions.Def_SizeRamsey_FiniteChecks
public import Definitions.Def_SizeRamsey_SmallGraphs
public import Theorems.Thm_SizeRamsey_Plan_c4Transversal_of_QTrans
public import Theorems.Thm_SizeRamsey_Plan_tau4_eq_of_certificates


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
namespace SizeRamsey.Plan
theorem _root_.solution {V : Type*} [Fintype V] {G : SimpleGraph V} (k : ℕ)
    (P : V → Finset V)
    (hP : ∀ v, v ∈ P v ∧ (P v).card = k ∧ QTrans G (P v))
    (hlower : ∀ S : Finset V, S.card < k → ¬ c4Transversal G S) (v₀ : V) :
    tau4 G = k ∧ PrescribedOptimal G := by
  have hk : tau4 G = k :=
    tau4_eq_of_certificates k ⟨P v₀, c4Transversal_of_QTrans (hP v₀).2.2, (hP v₀).2.1⟩ hlower
  refine ⟨hk, fun v => ⟨P v, (hP v).1, c4Transversal_of_QTrans (hP v).2.2, ?_⟩⟩
  rw [hk, (hP v).2.1]
end SizeRamsey.Plan
