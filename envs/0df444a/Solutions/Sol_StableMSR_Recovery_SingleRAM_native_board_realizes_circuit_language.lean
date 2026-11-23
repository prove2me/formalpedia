-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.native_board_realizes_circuit_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T00:14:57.79371+00:00
-- url     : https://prove2.me/submissions/d60620a5-02a2-42d9-9728-1f446beeff0c

import Definitions.Def_StableMSR_DenseSingletonCompilation
import Theorems.Thm_StableMSR_Recovery_SingleCircuit_three_records_per_separator_gate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleCircuit
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.BallCoverCatalog
open StableMSR.Recovery.WindowProfiles (subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Writes field)
open StableMSR.Recovery.SingleRAM
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)
private lemma move {n : ℕ} {A B : Board} {F H : ℕ→Cluster n}
    (size : A.size=B.size)
    (same : ∀q< A.size,A.tag q=B.tag q ∧ A.dest q=B.dest q ∧ A.child q=B.child q ∧ F q=H q)
    {p : ℕ} {L : List (Cluster n)} (tr : Trace A F p L) : Trace B H p L:=by
  have lit {q p : ℕ} (h : initial A q p) : initial B q p:=by
    obtain ⟨t,d,_,_⟩:=same q h.1;unfold initial at *;simpa only [←size,←t,←d] using h
  have prt {q p : ℕ} {j : ℤ} (h : port A j q p) : port B j q p:=by
    obtain ⟨t,d,c,_⟩:=same q h.1;unfold port at *;simpa only [←size,←t,←d,←c] using h
  induction tr with
  | literal init=>rw [(same _ init.1).2.2.2];exact .literal (lit init)
  | fork l r _ _ left right=>exact .fork (prt l) (prt r) ((same _ l.1).2.2.1 ▸ left) ((same _ r.1).2.2.1 ▸ right)
theorem solution (y : World) (g : Gates) (roots : ℕ→ℕ) (repr : denotes y g roots) (nonempty : 0< g.size) (zero : gateAt g 0=.atom [])
    (p : ℕ) (L : List (Cluster y.n)) : WindowMasks.Trace (board y) (block y) p L ↔ Language y.n g p L := by
  rw [←three_records_per_separator_gate y.n g roots nonempty zero p L]
  have size : (board y).size=(boardOf g roots).size:=repr.2.1
  have both (q : ℕ) (hq : q<3*g.size) :=repr.2.2 q hq
  constructor
  · exact move size (fun q h=>by obtain ⟨a,b,c,_,d⟩:=both q (by rw [←repr.2.1];exact h);exact ⟨a,b,c,d⟩)
  · exact move size.symm (fun q h=>by obtain ⟨a,b,c,_,d⟩:=both q h;exact ⟨a.symm,b.symm,c.symm,d.symm⟩)
