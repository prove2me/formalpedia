-- Prove2me | solution 1 for QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_odd_word
-- status  : ACCEPTED   (prove)
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:53:51.020297+00:00
-- url     : https://prove2.me/submissions/860be7da-6a63-44d6-a41f-f10acbe61e6c

/- Generated from Solutions.ThresholdPreparation by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition

/- Inline helpers retained from Solutions.BooleanFraming. -/
section


/-! Inverses and frame rules for the concrete Boolean straight-line compiler. -/
namespace QMAPerfectCompleteness.Main.BooleanCircuits





lemma evalCommand_outside {n : ℕ} (c : Command n) (x : Basis n) (w : Fin n)
    (hw : w ≠ c.target) : evalCommand c x w = x w := by
  cases c <;> exact Function.update_of_ne hw _ _

lemma eval_outside {n : ℕ} (p : List (Command n)) (x : Basis n) (w : Fin n)
    (hw : ∀ c ∈ p, w ≠ c.target) : eval p x w = x w := by
  induction p generalizing x with
  | nil => rfl
  | cons c p ih =>
    change eval p (evalCommand c x) w = _
    rw [ih _ (fun d hd => hw d (List.mem_cons_of_mem c hd)),
      evalCommand_outside c x w (hw c (List.mem_cons_self))]













end QMAPerfectCompleteness.Main.BooleanCircuits

end

/- Inline helpers retained from Solutions.RegisterCopies. -/
section


/-! Parallel classical register copies with distinct targets and unchanged source wires. -/
namespace QMAPerfectCompleteness.Main.RegisterCopies
open BooleanCircuits

variable {ι : Type*} [DecidableEq ι] {n : ℕ}
variable (source : ι → Fin n) (target : ι ↪ Fin n)
variable (hd : ∀ i j, source i ≠ target j)





lemma commands_target (js : List ι) (c : Command n) (hc : c ∈ commands source target hd js) :
    ∃ j ∈ js, c.target = target j := by
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc
  exact ⟨j,hj,rfl⟩

theorem eval_outside (js : List ι) (x : Basis n) (w : Fin n)
    (hw : ∀ j ∈ js, w ≠ target j) : eval (commands source target hd js) x w = x w := by
  apply BooleanCircuits.eval_outside
  intro c hc
  obtain ⟨j,hj,ht⟩ := commands_target source target hd js c hc
  rw [ht]
  exact hw j hj



/-- Copying each selected source once XORs it into its target, with every other wire fixed. -/
theorem eval_target (js : List ι) (hjs : js.Nodup) (x : Basis n) (j : ι) :
    eval (commands source target hd js) x (target j) =
      if j ∈ js then xor (x (target j)) (x (source j)) else x (target j) := by
  induction js generalizing x j with
  | nil => simp [commands,eval]
  | cons i js ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp hjs
    change eval (commands source target hd js)
      (Function.update x (target i) (xor (x (target i)) (x (source i)))) (target j) = _
    rw [ih hn]
    simp only [Function.update_of_ne (hd j i)]
    by_cases he : j=i
    · subst j; simp [hi]
    · have ht : target j ≠ target i := target.injective.ne he
      simp [he,ht]



end QMAPerfectCompleteness.Main.RegisterCopies

end



/-! Certificate-dependent binary threshold preparation. Arithmetic registers are explicit
physical wires; their values may be retained as certificate-dependent ancillary garbage. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.ThresholdPreparation
end QMAPerfectCompleteness.Main.ThresholdPreparation
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation
open BooleanCircuits ComparisonCircuits





namespace QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
end QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
section
open QMAPerfectCompleteness QMAPerfectCompleteness.Main QMAPerfectCompleteness.Main.ThresholdPreparation QMAPerfectCompleteness.Main.ThresholdPreparation.Layout
variable {k n : ℕ} (L : Layout k n)

















lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copyIndices_nodup : (copyIndices (k := k)).Nodup :=
  (List.nodup_finRange _).map finProdFinEquiv.symm.injective

@[simp] lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.mem_copyIndices (i : CopyIndex (k := k)) : i ∈ copyIndices := by
  apply List.mem_map.mpr
  exact ⟨finProdFinEquiv i,by simp,finProdFinEquiv.symm_apply_apply i⟩







theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_target (x : Basis n) (i : CopyIndex (k := k)) :
    L.copyState x (L.target i) = xor (x (L.target i)) (x (L.source i)) := by
  have h := RegisterCopies.eval_target L.source L.targetEmbedding L.source_ne_target
    copyIndices copyIndices_nodup x i
  simp only [mem_copyIndices,if_true] at h
  change L.copyState x (L.target i) = xor (x (L.target i)) (x (L.source i)) at h
  exact h

theorem QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_outside (x : Basis n) (w : Fin n) (hw : ∀ i, w ≠ L.target i) :
    L.copyState x w = x w :=
  RegisterCopies.eval_outside L.source L.targetEmbedding L.source_ne_target _ x w (fun i _ => hw i)







/-- A target word bit that is outside the selected copy positions is untouched. -/
lemma QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.copies_word_outside (x : Basis n) (d : Fin 6) (j : Fin (k+2))
    (hn : ∀ i : CopyIndex (k := k), d.val=i.1.val → j.val ≠ i.2.val+i.1.val%2) :
    L.copyState x (L.wire (.word d j)) = x (L.wire (.word d j)) := by
  apply L.copies_outside
  intro i h
  have hp := L.wire.injective h
  obtain ⟨hd,hj⟩ := Slot.word.inj hp
  have hdv := congrArg Fin.val hd
  have hjv := congrArg Fin.val hj
  exact hn i hdv hjv







/-- Odd-numbered word copies are the zero-extended source shifted left by one bit. -/
theorem solution (x : Basis n) (hz : ∀ d j, x (L.wire (.word d j)) = false)
    (d : Fin 4) (hd : d.val%2=1) :
    (fun j => L.copyState x (L.wire (.word ⟨d.val,(
                                                    have this : @LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) :=
                                                      @Fin.isLt (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d;
                                                    @Decidable.byContradiction (@LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                                      (Nat.decLt (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                                                      fun (a : Not (@LT.lt.{0} Nat instLTNat (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) =>
                                                      QMAPerfectCompleteness.Main.ThresholdPreparation.Layout.target_odd._proof_1 d hd a
                                                  )⟩ j))) =
      Fin.cons false (Fin.append (fun j => x (L.source (d,j))) (fun _ : Fin 1 => false)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.cons_zero]
    rw [L.copies_word_outside]
    · exact hz _ _
    · rintro ⟨e,i⟩ he hpos
      have heq : e=d := Fin.ext he.symm
      subst e
      simp only [Fin.val_zero,hd] at hpos
      omega
  · rw [Fin.cons_succ]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [← L.target_odd d hd j,L.copies_target]
      simp only [target,hz,Bool.false_xor,Fin.append_left]
    · rw [Fin.append_right]
      rw [L.copies_word_outside]
      · exact hz _ _
      · rintro ⟨e,i⟩ he hpos
        have heq : e=d := Fin.ext he.symm
        subst e
        simp only [Fin.val_succ,Fin.val_natAdd,hd] at hpos
        have hi := i.isLt
        omega
