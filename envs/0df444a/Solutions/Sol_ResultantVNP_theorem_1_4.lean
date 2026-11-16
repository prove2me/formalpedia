-- Prove2me | solution 1 for ResultantVNP.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T08:44:31.843334+00:00
-- url     : https://prove2.me/submissions/752eb5cc-2526-4767-ad28-b88276fe4058

import Mathlib
import Theorems.Thm_ResultantVNP_quadratic_to_tensor_circuits
import Theorems.Thm_ResultantVNP_theorem_1_4_symmetric_tensor

set_option autoImplicit false

namespace HyperdetCircuits

private def renameNode {σ τ : Type} (ρ : σ → τ) :
    ResultantVNP.Node σ → ResultantVNP.Node τ
  | .var x => .var (ρ x)
  | .const a => .const a
  | .add i j => .add i j
  | .mul i j => .mul i j

private lemma readsBelow_rename {σ τ : Type} (ρ : σ → τ)
    (nd : ResultantVNP.Node σ) (k : ℕ) :
    (renameNode ρ nd).ReadsBelow k = nd.ReadsBelow k := by
  cases nd <;> rfl

/-- Identifying or relabelling variables preserves the circuit graph. -/
def renameCircuit {σ τ : Type} (ρ : σ → τ)
    (C : ResultantVNP.Circuit σ) : ResultantVNP.Circuit τ where
  nodes := C.nodes.map (renameNode ρ)
  nonempty := by
    intro h
    exact C.nonempty (List.eq_nil_of_map_eq_nil h)
  wf := by
    intro k hk
    have h := C.wf k (by simpa only [List.length_map] using hk)
    simpa only [List.getElem_map, readsBelow_rename] using h

private lemma eval_rename {σ τ : Type} (ρ : σ → τ)
    (vals : List (MvPolynomial σ ℂ)) (nd : ResultantVNP.Node σ) :
    (renameNode ρ nd).eval (vals.map (MvPolynomial.rename ρ)) =
      MvPolynomial.rename ρ (nd.eval vals) := by
  have hg (i : ℕ) :
      (vals.map (MvPolynomial.rename ρ)).getD i 0 =
        MvPolynomial.rename ρ (vals.getD i 0) := by
    simpa only [map_zero] using
      (List.getD_map (l := vals) (d := (0 : MvPolynomial σ ℂ))
        (n := i) (MvPolynomial.rename ρ))
  cases nd <;> simp only [renameNode, ResultantVNP.Node.eval, hg,
    MvPolynomial.rename_X, MvPolynomial.rename_C, map_add, map_mul]

private lemma fold_rename {σ τ : Type} (ρ : σ → τ)
    (nodes : List (ResultantVNP.Node σ)) (vals : List (MvPolynomial σ ℂ)) :
    (nodes.map (renameNode ρ)).foldl (fun vs nd => vs ++ [nd.eval vs])
        (vals.map (MvPolynomial.rename ρ)) =
      (nodes.foldl (fun vs nd => vs ++ [nd.eval vs]) vals).map (MvPolynomial.rename ρ) := by
  induction nodes generalizing vals with
  | nil => rfl
  | cons nd nodes ih =>
    simp only [List.map_cons, List.foldl_cons]
    simpa only [List.map_append, List.map_cons, List.map_nil, eval_rename] using
      ih (vals ++ [nd.eval vals])

theorem renameCircuit_value {σ τ : Type} (ρ : σ → τ)
    (C : ResultantVNP.Circuit σ) :
    (renameCircuit ρ C).value = MvPolynomial.rename ρ C.value := by
  have hv : (renameCircuit ρ C).values = C.values.map (MvPolynomial.rename ρ) := by
    simpa only [ResultantVNP.Circuit.values, renameCircuit, List.map_nil] using
      fold_rename ρ C.nodes []
  unfold ResultantVNP.Circuit.value
  rw [hv]
  simpa only [map_zero] using
    (List.getLastD_map (f := MvPolynomial.rename ρ) (l := C.values)
      (a := (0 : MvPolynomial σ ℂ)))

theorem renameCircuit_size {σ τ : Type} (ρ : σ → τ)
    (C : ResultantVNP.Circuit σ) : (renameCircuit ρ C).size = C.size := by
  have hg : ∀ nd : ResultantVNP.Node σ,
      (renameNode ρ nd).isGate = nd.isGate := by intro nd; cases nd <;> rfl
  simp [ResultantVNP.Circuit.size, renameCircuit, List.countP_map, Function.comp_def, hg]

end HyperdetCircuits

/-!
CONDITIONAL PROOF-SKETCH, NOT A COMPLETE PROOF OF THE MAIN THEOREM.

Target: ResultantVNP.theorem_1_4
Prove2Me UUID: 5c7c7594-6248-409b-a757-48e52a6a9fe7

This reduces the exact main target to:
1. the proposed quadratic-to-general-tensor circuit-specialization lemma;
2. the existing symmetric-tensor clause of Theorem 1.4 (an open milestone).

The further restriction from general to symmetric tensors is proved here:
identify the three-index variables using renameCircuit. Its value is the
renamed polynomial and its gate count is exactly unchanged.

No import of the target theorem itself is used. There are no proof holes in
this reduction file. Its imported children are open, so its axiom report
contains sorryAx; this file must never be reported as an unconditional proof.
-/

theorem solution (𝓡 : ResultantVNP.ResultantSystem)
    (h : ResultantVNP.HasPolySizeCircuits
      (fun n => MvPolynomial.map (Int.castRingHom ℂ) (ResultantVNP.quadRes 𝓡 n))) :
    ResultantVNP.VP = ResultantVNP.VNP := by
  apply ResultantVNP.theorem_1_4_symmetric_tensor 𝓡
  obtain ⟨c, hc⟩ := ResultantVNP.quadratic_to_tensor_circuits 𝓡 h
  refine ⟨c, ?_⟩
  intro n hn
  obtain ⟨C, hC, hsize⟩ := hc n hn
  let ρ : (Fin n × Fin n × Fin n) → Sym (Fin n) 3 :=
    fun t => t.1 ::ₛ t.2.1 ::ₛ t.2.2 ::ₛ Sym.nil
  refine ⟨HyperdetCircuits.renameCircuit ρ C, ?_, ?_⟩
  · rw [HyperdetCircuits.renameCircuit_value, hC]
    exact (MvPolynomial.map_rename (Int.castRingHom ℂ) ρ
      (ResultantVNP.tensorDet 𝓡 n)).symm
  · simpa only [HyperdetCircuits.renameCircuit_size] using hsize

#print axioms solution
