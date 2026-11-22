-- Prove2me | solution 1 for ShiShallow.exists_majority_readout_at_wires_layerOk_depth
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T08:52:46.716698+00:00
-- url     : https://prove2.me/submissions/40994d11-e88c-4fe6-9bce-94330613a61e

import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_exists_toffoli_at_wires_layerOk_depth
import Theorems.Thm_ShiShallow_runLayered_append_action_readout

set_option autoImplicit false

open ShiShallow

/-!
# Majority-of-three readout, with `LayerOk` and an explicit depth

Three Toffoli blocks share the scratch wire `s` as target, with control pairs
`(w1,w2)`, `(w2,w3)`, `(w1,w3)`.  Each block is the ACCEPTED atom
`ShiShallow.exists_toffoli_at_wires_layerOk_depth`, of depth `37`, so the composite
has depth `37 + 37 + 37 = 111`.

## Append order

`runLayered_append_action_readout` puts the SECOND circuit's reindexing INSIDE:
`runLayered (cA ++ cR) psi = fun x => fA psi (uR x)`.  Layers act left to right and
pull-back reverses, so the circuit written FIRST in the append supplies the
OUTERMOST update, i.e. the LAST XOR to be accumulated onto wire `s`.  Writing
`(c12 ++ c23) ++ c13` therefore accumulates, innermost first,
`x s -> x s ^ C -> (x s ^ C) ^ B -> ((x s ^ C) ^ B) ^ A`
with `A = x w1 & x w2`, `B = x w2 & x w3`, `C = x w1 & x w3`, and the target value
is `x s ^ ((A ^ B) ^ C)`.  These agree by associativity and commutativity of `xor`,
which is `shiMR_xor_rearrange`.  (Any of the six orders would work, since `xor` is
abelian; this one keeps the reassociation lemma to a single rewrite.)

## `majority3_accum` was NOT usable

`ShiShallow.majority3_accum` is stated over an abstract `TOF : Fin n -> Fin n -> Fin n ->
QState n -> QState n` with `hTOF` demanded at ALL wire triples, including degenerate
ones such as `p = q`, where the Toffoli law is false for any unitary implementation.
Our atom is a per-triple existential, so no such total `TOF` is in hand.  The
three-fold update algebra is done directly below instead.
-/

/-- Reassociating the accumulated XOR.  `d` is the incoming scratch bit; the three
Toffolis contribute `c`, then `b`, then `a`, so the accumulation is left-nested in the
reverse of the stated order. -/
private theorem shiMR_xor_rearrange (d a b c : Bool) :
    xor (xor (xor d c) b) a = xor d (xor (xor a b) c) := by
  first
    | (cases d <;> cases a <;> cases b <;> cases c <;> rfl)
    | (decide +revert)

/-- Majority-of-three XORed into a scratch wire, at arbitrary wires of any register,
carrying layer well-formedness and an explicit depth of `111`. -/
theorem solution {N : ℕ} (w1 w2 w3 s : Fin N)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) :
    ∃ c : Layered N,
      (∀ ψ : QState N, runLayered c ψ
          = fun x => ψ (Function.update x s
              (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 111 := by
  obtain ⟨c12, hc12, hok12, hd12⟩ :=
    ShiShallow.exists_toffoli_at_wires_layerOk_depth w1 w2 s h12 h1s h2s
  obtain ⟨c23, hc23, hok23, hd23⟩ :=
    ShiShallow.exists_toffoli_at_wires_layerOk_depth w2 w3 s h23 h2s h3s
  obtain ⟨c13, hc13, hok13, hd13⟩ :=
    ShiShallow.exists_toffoli_at_wires_layerOk_depth w1 w3 s h13 h1s h3s
  refine ⟨(c12 ++ c23) ++ c13, ?_, ?_, ?_⟩
  · -- semantics
    intro ψ
    have hstep1 : ∀ χ : QState N, runLayered (c12 ++ c23) χ
        = fun x => runLayered c12 χ (Function.update x s (xor (x s) (x w2 && x w3))) := by
      intro χ
      exact ShiShallow.runLayered_append_action_readout c12 c23
        (fun ρ => runLayered c12 ρ)
        (fun x => Function.update x s (xor (x s) (x w2 && x w3)))
        (fun _ => rfl) hc23 χ
    have hstep2 : runLayered ((c12 ++ c23) ++ c13) ψ
        = fun x => runLayered (c12 ++ c23) ψ
            (Function.update x s (xor (x s) (x w1 && x w3))) :=
      ShiShallow.runLayered_append_action_readout (c12 ++ c23) c13
        (fun ρ => runLayered (c12 ++ c23) ρ)
        (fun x => Function.update x s (xor (x s) (x w1 && x w3)))
        (fun _ => rfl) hc13 ψ
    rw [hstep2, hstep1 ψ, hc12]
    funext x
    (try dsimp only)
    have e1 : ∀ v : Bool, Function.update x s v w1 = x w1 :=
      fun v => Function.update_of_ne h1s v x
    have e2 : ∀ v : Bool, Function.update x s v w2 = x w2 :=
      fun v => Function.update_of_ne h2s v x
    have e3 : ∀ v : Bool, Function.update x s v w3 = x w3 :=
      fun v => Function.update_of_ne h3s v x
    have es : ∀ v : Bool, Function.update x s v s = v :=
      fun v => Function.update_self s v x
    have eid : ∀ u v : Bool,
        Function.update (Function.update x s u) s v = Function.update x s v :=
      fun u v => Function.update_idem u v x
    simp only [e1, e2, e3, es, eid]
    all_goals
      first
        | (rfl; done)
        | (rw [shiMR_xor_rearrange]; done)
        | (exact congrArg ψ (congrArg (Function.update x s)
              (shiMR_xor_rearrange (x s) (x w1 && x w2) (x w2 && x w3) (x w1 && x w3))); done)
  · -- LayerOk on every layer of the append
    intro l hl
    rcases List.mem_append.mp hl with hl1 | hl1
    · rcases List.mem_append.mp hl1 with hl2 | hl2
      · exact hok12 l hl2
      · exact hok23 l hl2
    · exact hok13 l hl1
  · -- depth = 37 + 37 + 37
    simp only [depth, List.length_append] at hd12 hd23 hd13 ⊢
    omega
