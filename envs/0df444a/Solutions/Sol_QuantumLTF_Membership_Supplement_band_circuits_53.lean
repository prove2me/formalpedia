-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.band_circuits_53
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T08:02:36.535836+00:00
-- url     : https://prove2.me/submissions/9743c4b6-d9c7-4636-99fe-c5197c2df1ea

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_goodBasis53

set_option autoImplicit false

namespace BandCircuits53Work

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement Thm49Primitives Thm410Router

/-! ### 1. Generic Combinators & `zeroReflectCircuit` -/

lemma bitsToNatLSB_rev {q : ℕ} (b : Qubits q) :
    bitsToNatLSB (fun j : Fin q => b j.rev) = bitsToNat b := by
  dsimp only [bitsToNatLSB, bitsToNat]
  refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin q)) _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.val_rev]
  have hi := i.isLt
  have heq : i.1 = q - 1 - (q - (i.1 + 1)) := by omega
  rw [← heq]

lemma padZero_eq_append {main anc : ℕ} (x : Qubits main) :
    padZero main anc x = Fin.append x (fun _ : Fin anc => false) := rfl

lemma act_mapWires_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) :
    let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain))) := by
  intro embMain
  have h := act_mapWires_implementsOnClean lc (permMat f) hlc emb z hclean
  dsimp only at h
  dsimp only [embMain]
  rw [h, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans emb)))]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private def skipMidEmb (m anc : ℕ) : Fin (m + (1 + anc)) ↪ Fin ((m + 1) + (1 + anc)) where
  toFun w := if w.1 < m then ⟨w.1, by omega⟩ else ⟨w.1 + 1, by have := w.isLt; omega⟩
  inj' a b hab := by
    have ha := a.isLt; have hb := b.isLt
    have hval := congrArg Fin.val hab
    dsimp only at hval
    by_cases ha1 : a.1 < m <;> by_cases hb1 : b.1 < m
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext hval
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; omega
    · simp only [ha1, hb1, ↓reduceIte] at hval; exact Fin.ext (by omega)

@[simp] private lemma skipMidEmb_val (m anc : ℕ) (w : Fin (m + (1 + anc))) :
    (skipMidEmb m anc w).1 = if w.1 < m then w.1 else w.1 + 1 := by
  change (if w.1 < m then (⟨w.1, by omega⟩ : Fin ((m + 1) + (1 + anc)))
    else ⟨w.1 + 1, by have := w.isLt; omega⟩).1 = _
  split_ifs <;> rfl

noncomputable def markerGateOfFlag {m anc : ℕ} (flagCompute : LayeredCircuit (m + (1 + anc))) :
    LayeredCircuit ((m + 1) + (1 + anc)) :=
  let emb := skipMidEmb m anc
  let fc := flagCompute.mapWires emb
  let tgt : Fin ((m + 1) + (1 + anc)) := ⟨m, by omega⟩
  let flagW : Fin ((m + 1) + (1 + anc)) := ⟨m + 1, by omega⟩
  have hne : flagW ≠ tgt := by
    intro h; have := congrArg Fin.val h; dsimp [flagW, tgt] at this; omega
  fc.seq ((cnotGate flagW tgt hne).seq fc.adj)

lemma markerGateOfFlag_size {m anc : ℕ} (flagCompute : LayeredCircuit (m + (1 + anc))) :
    (markerGateOfFlag flagCompute).size = 2 * flagCompute.size + 1 := by
  simp [markerGateOfFlag]; omega

lemma markerGateOfFlag_implements {m anc : ℕ} (flagCompute : LayeredCircuit (m + (1 + anc)))
    (P : Qubits m → Bool)
    (hcomp : ∀ x : Qubits m, ∃ z' : Qubits (m + (1 + anc)),
      act flagCompute.unitary (ket (padZero m (1 + anc) x)) = ket z' ∧
      z' ⟨m, by omega⟩ = P x) :
    ∀ (x : Qubits m) (b : Bool),
      act (markerGateOfFlag flagCompute).unitary
          (ket (Fin.append (Fin.snoc (α := fun _ => Bool) x b) (fun _ : Fin (1 + anc) => false))) =
        ket (Fin.append (Fin.snoc (α := fun _ => Bool) x (xor b (P x)))
          (fun _ : Fin (1 + anc) => false)) := by
  intro x b
  let emb := skipMidEmb m anc
  let fc := flagCompute.mapWires emb
  let tgt : Fin ((m + 1) + (1 + anc)) := ⟨m, by omega⟩
  let flagW : Fin ((m + 1) + (1 + anc)) := ⟨m + 1, by omega⟩
  have hne : flagW ≠ tgt := by
    intro h; have := congrArg Fin.val h; dsimp [flagW, tgt] at this; omega
  let z0 : Qubits ((m + 1) + (1 + anc)) :=
    Fin.append (Fin.snoc (α := fun _ => Bool) x b) (fun _ : Fin (1 + anc) => false)
  have hz0_comp : z0 ∘ emb = padZero m (1 + anc) x := by
    funext w
    rw [Function.comp_apply, padZero_eq_append]
    dsimp only [z0]
    by_cases hw : w.1 < m
    · have heq : emb w = Fin.castAdd (1 + anc) (Fin.castSucc ⟨w.1, hw⟩) := by
        apply Fin.ext; simp [emb, hw]
      rw [heq, Fin.append_left, Fin.snoc_castSucc]
      have hw_cast : w = Fin.castAdd (1 + anc) ⟨w.1, hw⟩ := Fin.ext rfl
      conv_rhs => rw [hw_cast]
      rw [Fin.append_left]
    · have heq : emb w = Fin.natAdd (m + 1) ⟨w.1 - m, by have := w.isLt; omega⟩ := by
        apply Fin.ext; simp [emb, hw]; omega
      rw [heq, Fin.append_right]
      have hw_nat : w = Fin.natAdd m ⟨w.1 - m, by have := w.isLt; omega⟩ := by
        apply Fin.ext; simp; omega
      conv_rhs => rw [hw_nat]
      rw [Fin.append_right]
  rcases hcomp x with ⟨z', hfc0, hz'_flag⟩
  let z1 := updateOn emb z0 z'
  have hfc_act : act fc.unitary (ket z0) = ket z1 := by
    refine act_mapWires_ket flagCompute emb z0 z' (by rwa [hz0_comp]) z1 ?_ ?_
    · exact updateOn_comp emb z0 z'
    · intro i hi; exact updateOn_apply_not_mem emb z0 z' hi
  have htgt_not_mem : tgt ∉ Finset.univ.image emb := by
    rw [Finset.mem_image]
    rintro ⟨w, _, hw⟩
    have hval := congrArg Fin.val hw
    dsimp only [emb, tgt] at hval
    rw [skipMidEmb_val] at hval
    split_ifs at hval <;> omega
  have hfc_uses : fc.UsesOnly (Finset.univ.image emb) :=
    LayeredCircuit.mapWires_usesOnly emb flagCompute (fun _ _ _ _ _ => Finset.mem_univ _)
  have hz1_tgt : z1 tgt = b := by
    have htgt_not_range : tgt ∉ Set.range emb := by
      rintro ⟨w, hw⟩
      exact htgt_not_mem (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩)
    dsimp only [z1]
    rw [updateOn_apply_not_mem emb z0 z' htgt_not_range]
    have heq : tgt = Fin.castAdd (1 + anc) (Fin.last m) := Fin.ext rfl
    dsimp only [z0]
    rw [heq, Fin.append_left, Fin.snoc_last]
  have hz1_flag : z1 flagW = P x := by
    have hflag_eq : flagW = emb ⟨m, by omega⟩ := by
      apply Fin.ext; simp [emb, flagW]
    rw [hflag_eq]
    change updateOn emb z0 z' (emb ⟨m, by omega⟩) = P x
    rw [updateOn_apply_emb, hz'_flag]
  have hupd_adj : act fc.adj.unitary (ket (Function.update z1 tgt (xor b (P x)))) =
      ket (Function.update z0 tgt (xor b (P x))) := by
    have hupd := act_ket_update_of_not_mem fc hfc_uses tgt htgt_not_mem hfc_act (xor b (P x))
    rw [← hupd, ← act_mul, LayeredCircuit.adj_unitary,
      Matrix.mem_unitaryGroup_iff'.mp fc.unitary_mem_unitaryGroup, act_one]
  dsimp only [markerGateOfFlag]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act fc.adj.unitary (act (cnotGate flagW tgt hne).unitary (act fc.unitary (ket z0))) = _
  rw [hfc_act, act_cnotGate_ket, hz1_tgt, hz1_flag, hupd_adj]
  congr 1
  funext w
  by_cases hw : w = tgt
  · subst hw
    rw [Function.update_self]
    have heq : tgt = Fin.castAdd (1 + anc) (Fin.last m) := Fin.ext rfl
    rw [heq, Fin.append_left, Fin.snoc_last]
  · rw [Function.update_of_ne hw]
    dsimp only [z0]
    by_cases hlt : w.1 < m
    · have hw_cast : w = Fin.castAdd (1 + anc) (Fin.castSucc ⟨w.1, hlt⟩) := Fin.ext rfl
      rw [hw_cast, Fin.append_left, Fin.append_left, Fin.snoc_castSucc, Fin.snoc_castSucc]
    · have hne_m : w.1 ≠ m := fun h => hw (Fin.ext h)
      have hgt : m + 1 ≤ w.1 := by omega
      have hw_nat : w = Fin.natAdd (m + 1) ⟨w.1 - (m + 1), by have := w.isLt; omega⟩ := by
        apply Fin.ext; simp; omega
      rw [hw_nat, Fin.append_right, Fin.append_right]

private noncomputable def zeroFlagCompute (m : ℕ) : LayeredCircuit (m + (1 + m)) :=
  (multiEqCtrl1 m (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires
    (finCongr (Nat.add_assoc m 1 m)).toEmbedding

private lemma zeroFlagCompute_size (m : ℕ) :
    (zeroFlagCompute m).size ≤ 12 * (m + 1) := by
  rw [zeroFlagCompute, LayeredCircuit.mapWires_size]
  exact multiEqCtrl1_size m (fun _ => false) pauliX pauliX_mem_unitaryGroup

private lemma zeroFlagCompute_implements (m : ℕ) (x : Qubits m) :
    ∃ z' : Qubits (m + (1 + m)),
      act (zeroFlagCompute m).unitary (ket (padZero m (1 + m) x)) = ket z' ∧
      z' ⟨m, by omega⟩ = decide (x = fun _ => false) := by
  let e := (finCongr (Nat.add_assoc m 1 m)).toEmbedding
  have he_lt : ∀ i : Fin (m + 1 + m), (e i).1 = i.1 := fun _ => rfl
  let lc := multiEqCtrl1 m (fun _ => false) pauliX pauliX_mem_unitaryGroup
  have hclean : ∀ j : Fin m, padZero m (1 + m) x (e (Fin.natAdd (m + 1) j)) = false := fun j => by
    have heq : e (Fin.natAdd (m + 1) j) = Fin.natAdd m ⟨1 + j.1, by omega⟩ := by
      apply Fin.ext; simp [e]; omega
    rw [heq, padZero_natAdd]
  have hlc_perm : lc.ImplementsOnClean (permMat fun v : Qubits (m + 1) =>
      Function.update v ⟨m, Nat.lt_succ_self m⟩
        (xor (v ⟨m, Nat.lt_succ_self m⟩) (decide (∀ i : Fin m, v ⟨i.1, by omega⟩ = false)))) := by
    have h := multiEqCtrl1_implements m (fun _ => false) pauliX pauliX_mem_unitaryGroup
    have heq : eqCtrlMat m (fun _ => false) pauliX =
        permMat (fun v : Qubits (m + 1) =>
          Function.update v ⟨m, Nat.lt_succ_self m⟩
            (xor (v ⟨m, Nat.lt_succ_self m⟩) (decide (∀ i : Fin m, v ⟨i.1, by omega⟩ = false)))) := by
      ext y z
      simp only [eqCtrlMat, permMat, Matrix.of_apply]
      by_cases hyz : ∀ i : Fin m, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
      · rw [if_pos hyz]
        by_cases hall : ∀ i : Fin m, z ⟨i.1, by omega⟩ = false
        · rw [if_pos hall]
          have hy_eq : (y = Function.update z ⟨m, Nat.lt_succ_self m⟩
              (xor (z ⟨m, Nat.lt_succ_self m⟩) (decide (∀ i : Fin m, z ⟨i.1, by omega⟩ = false)))) ↔
              y ⟨m, Nat.lt_succ_self m⟩ = !z ⟨m, Nat.lt_succ_self m⟩ := by
            simp only [decide_eq_true hall, Bool.xor_true]
            constructor
            · intro h; rw [h, Function.update_self]
            · intro h; funext k
              rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
              · have hne : k'.castSucc ≠ ⟨m, Nat.lt_succ_self m⟩ := Fin.ne_of_val_ne (by simp; omega)
                rw [Function.update_of_ne hne]; exact hyz k'
              · have hlast : Fin.last m = ⟨m, Nat.lt_succ_self m⟩ := rfl
                rw [hlast, Function.update_self]; exact h
          by_cases hym : y ⟨m, Nat.lt_succ_self m⟩ = !z ⟨m, Nat.lt_succ_self m⟩
          · rw [if_pos (hy_eq.mpr hym), hym]
            cases z ⟨m, Nat.lt_succ_self m⟩ <;> simp [pauliX]
          · rw [if_neg (mt hy_eq.mp hym)]
            cases hzm : z ⟨m, Nat.lt_succ_self m⟩ <;> cases hym' : y ⟨m, Nat.lt_succ_self m⟩ <;>
              simp [pauliX, hzm, hym'] at hym ⊢
        · rw [if_neg hall]
          have hy_eq : (y = Function.update z ⟨m, Nat.lt_succ_self m⟩
              (xor (z ⟨m, Nat.lt_succ_self m⟩) (decide (∀ i : Fin m, z ⟨i.1, by omega⟩ = false)))) ↔
              y ⟨m, Nat.lt_succ_self m⟩ = z ⟨m, Nat.lt_succ_self m⟩ := by
            simp only [decide_eq_false hall, Bool.xor_false, Function.update_eq_self]
            constructor
            · intro h; rw [h]
            · intro h; funext k
              rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
              · exact hyz k'
              · exact h
          by_cases hym : y ⟨m, Nat.lt_succ_self m⟩ = z ⟨m, Nat.lt_succ_self m⟩
          · rw [if_pos hym, if_pos (hy_eq.mpr hym)]
          · rw [if_neg hym, if_neg (mt hy_eq.mp hym)]
      · rw [if_neg hyz]
        symm; rw [if_neg]
        intro h; apply hyz; intro i
        have h1 := congrFun h ⟨i.1, by omega⟩
        have hne : (⟨i.1, by omega⟩ : Fin (m + 1)) ≠ ⟨m, Nat.lt_succ_self m⟩ :=
          Fin.ne_of_val_ne (by simp; omega)
        rwa [Function.update_of_ne hne] at h1
    rwa [← heq]
  have hact := act_mapWires_perm lc _ hlc_perm e (padZero m (1 + m) x) hclean
  refine ⟨_, hact, ?_⟩
  let embMain := (Fin.castAddEmb m).trans e
  have hm_eq : (⟨m, by omega⟩ : Fin (m + (1 + m))) = embMain ⟨m, Nat.lt_succ_self m⟩ := by
    apply Fin.ext; simp [embMain, e]
  rw [hm_eq, updateOn_apply_emb, Function.update_self]
  have hm_nat : embMain ⟨m, Nat.lt_succ_self m⟩ = Fin.natAdd m ⟨0, by omega⟩ := by
    apply Fin.ext; simp [embMain, e]
  change xor (padZero m (1 + m) x (embMain ⟨m, Nat.lt_succ_self m⟩)) _ = _
  rw [hm_nat, padZero_natAdd, Bool.false_xor]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro hall; funext i
    have hi : embMain ⟨i.1, by omega⟩ = Fin.castAdd (1 + m) i := Fin.ext rfl
    have h1 := hall i
    change padZero m (1 + m) x (embMain ⟨i.1, by omega⟩) = false at h1
    rwa [hi, padZero_castAdd] at h1
  · intro hx i
    have hi : embMain ⟨i.1, by omega⟩ = Fin.castAdd (1 + m) i := Fin.ext rfl
    change padZero m (1 + m) x (embMain ⟨i.1, by omega⟩) = false
    rw [hi, padZero_castAdd, hx]

noncomputable def zeroReflectCircuit (n q a : ℕ) :
    Circuit gates12 ((n * q + 1 + a) + (1 + (n * q + 1 + a))) :=
  (phaseGateOfFlag (zeroFlagCompute (n * q + 1 + a))).toCircuit

lemma zeroReflectCircuit_size (n q a : ℕ) :
    (zeroReflectCircuit n q a).length ≤ 49 * (n * q + a + 1) := by
  change (phaseGateOfFlag (zeroFlagCompute (n * q + 1 + a))).size ≤ _
  rw [phaseGateOfFlag_size]
  have h1 := zeroFlagCompute_size (n * q + 1 + a)
  omega

lemma zeroReflectCircuit_act (n q a : ℕ) (z : Qubits (n * q + 1 + a)) :
    act (zeroReflectCircuit n q a).unitary
        (ket (Fin.append z (fun _ : Fin (1 + (n * q + 1 + a)) => false))) =
      (if z = (fun _ => false) then (-1 : ℂ) else 1) •
        ket (Fin.append z (fun _ : Fin (1 + (n * q + 1 + a)) => false)) := by
  have himp := phaseGateOfFlag_implements (zeroFlagCompute (n * q + 1 + a))
    (fun x : Qubits (n * q + 1 + a) => decide (x = fun _ => false))
    (zeroFlagCompute_implements (n * q + 1 + a))
  change act (phaseGateOfFlag (zeroFlagCompute (n * q + 1 + a))).unitary
    (ket (padZero (n * q + 1 + a) (1 + (n * q + 1 + a)) z)) = _
  rw [act_ket_of_implementsOnClean himp z, Finset.sum_eq_single z]
  · simp [diagPhaseMat, padZero_eq_append]
  · intro y _ hy; simp [diagPhaseMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### 2. `firstHitSwapCircuit` -/

private lemma fin_prod_lt {a b : ℕ} (i : Fin a) (j : Fin b) : i.1 * b + j.1 < a * b := by
  have h := (finProdFinEquiv (i, j)).isLt
  simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk] at h
  linarith

private def fhsWireBlock {R m_reg : ℕ} (i : Fin R) (b : Fin m_reg) :
    Fin ((R * m_reg) + R + 2 * R) :=
  ⟨i.1 * m_reg + b.1, by have := fin_prod_lt i b; omega⟩

private def fhsWireFlag {R m_reg : ℕ} (j : Fin R) : Fin ((R * m_reg) + R + 2 * R) :=
  ⟨R * m_reg + j.1, by have := j.isLt; omega⟩

private def fhsWirePref {R m_reg : ℕ} (j : Fin R) : Fin ((R * m_reg) + R + 2 * R) :=
  ⟨R * m_reg + R + j.1, by have := j.isLt; omega⟩

private def fhsWireHit {R m_reg : ℕ} (j : Fin R) : Fin ((R * m_reg) + R + 2 * R) :=
  ⟨R * m_reg + 2 * R + j.1, by have := j.isLt; omega⟩

private lemma fhsWirePref_inj {R m_reg : ℕ} :
    Function.Injective (fhsWirePref (R := R) (m_reg := m_reg)) := by
  intro a b h; have := congrArg Fin.val h; dsimp [fhsWirePref] at this; exact Fin.ext (by omega)

private lemma fhsWireHit_inj {R m_reg : ℕ} :
    Function.Injective (fhsWireHit (R := R) (m_reg := m_reg)) := by
  intro a b h; have := congrArg Fin.val h; dsimp [fhsWireHit] at this; exact Fin.ext (by omega)

private lemma fhsWireBlock_inj {R m_reg : ℕ} {i₁ i₂ : Fin R} {b₁ b₂ : Fin m_reg}
    (h : fhsWireBlock i₁ b₁ = fhsWireBlock i₂ b₂) : i₁ = i₂ ∧ b₁ = b₂ := by
  have hv := congrArg Fin.val h
  dsimp [fhsWireBlock] at hv
  have h1 : finProdFinEquiv (i₁, b₁) = finProdFinEquiv (i₂, b₂) := Fin.ext (by
    simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk]
    linarith)
  have h2 := finProdFinEquiv.injective h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

private noncomputable def fhsPrefPrefix (R m_reg : ℕ) (hR : 1 ≤ R) :
    (k : ℕ) → k ≤ R → LayeredCircuit ((R * m_reg) + R + 2 * R)
  | 0, _ => LayeredCircuit.id _
  | 1, _ => pauliXGate (fhsWirePref ⟨0, hR⟩)
  | k + 2, hk =>
    let prev := fhsPrefPrefix R m_reg hR (k + 1) (by omega)
    let pCurr := fhsWirePref (R := R) (m_reg := m_reg) ⟨k, by omega⟩
    let pNext := fhsWirePref (R := R) (m_reg := m_reg) ⟨k + 1, hk⟩
    let fCurr := fhsWireFlag (R := R) (m_reg := m_reg) ⟨k, by omega⟩
    have hpf : pCurr ≠ fCurr := by
      intro h; have := congrArg Fin.val h; dsimp [pCurr, fCurr, fhsWirePref, fhsWireFlag] at this; omega
    have hpn : pCurr ≠ pNext := fun h => by
      have := congrArg Fin.val (fhsWirePref_inj h); dsimp at this; omega
    have hfn : fCurr ≠ pNext := by
      intro h; have := congrArg Fin.val h; dsimp [fCurr, pNext, fhsWireFlag, fhsWirePref] at this; omega
    prev.seq ((pauliXGate fCurr).seq ((toffoliOn pCurr fCurr pNext hpf hpn hfn).seq (pauliXGate fCurr)))

private lemma fhsPrefPrefix_size (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R) :
    (fhsPrefPrefix R m_reg hR k hk).size ≤ 7 * k := by
  induction k with
  | zero => simp [fhsPrefPrefix]
  | succ k ih =>
    cases k with
    | zero => simp [fhsPrefPrefix]
    | succ k' =>
      have hk1 : k' + 1 ≤ R := by omega
      have hih := ih hk1
      simp only [fhsPrefPrefix, LayeredCircuit.seq_size, pauliXGate_size, toffoliOn_size]
      omega

private lemma fhsPrefPrefix_act (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R)
    (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    let z0 : Qubits ((R * m_reg) + R + 2 * R) :=
      Fin.append (Fin.append (flatReg R m_reg blocks) f) (fun _ : Fin (2 * R) => false)
    let z' : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if _ : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + k then
        decide (∀ t : Fin R, t.1 < w.1 - (R * m_reg + R) → f t = false)
      else z0 w
    act (fhsPrefPrefix R m_reg hR k hk).unitary (ket z0) = ket z' := by
  intro z0
  induction k with
  | zero =>
    simp only [fhsPrefPrefix, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w
    rw [dif_neg (by omega)]
  | succ k ih =>
    cases k with
    | zero =>
      simp only [fhsPrefPrefix, act_pauliXGate_ket]
      congr 1; funext w
      by_cases hw : w = fhsWirePref ⟨0, hR⟩
      · subst hw
        have hw0 : (fhsWirePref (R := R) (m_reg := m_reg) ⟨0, hR⟩ : Fin ((R * m_reg) + R + 2 * R)) =
            Fin.natAdd ((R * m_reg) + R) ⟨0, by omega⟩ := by
          apply Fin.ext; simp [fhsWirePref]
        rw [Function.update_self, hw0]
        dsimp only [z0]
        rw [Fin.append_right]
        rw [dif_pos (by simp)]
        simp
      · rw [Function.update_of_ne hw]
        have hnot : ¬ (R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + 1) := by
          intro h; apply hw; apply Fin.ext; dsimp [fhsWirePref]; omega
        rw [dif_neg hnot]
    | succ k' =>
      have hk1 : k' + 1 ≤ R := by omega
      let zMid : Qubits ((R * m_reg) + R + 2 * R) := fun u =>
        if h : R * m_reg + R ≤ u.1 ∧ u.1 < R * m_reg + R + (k' + 1) then
          decide (∀ t : Fin R, t.1 < u.1 - (R * m_reg + R) → f t = false)
        else z0 u
      have hih : act (fhsPrefPrefix R m_reg hR (k' + 1) hk1).unitary (ket z0) = ket zMid := ih hk1
      dsimp only [fhsPrefPrefix]
      simp only [LayeredCircuit.seq_unitary, act_mul]
      rw [hih, act_pauliXGate_ket, act_toffoliOn_ket, act_pauliXGate_ket]
      congr 1; funext w
      let pCurr := fhsWirePref (R := R) (m_reg := m_reg) ⟨k', by omega⟩
      let pNext := fhsWirePref (R := R) (m_reg := m_reg) ⟨k' + 1, hk⟩
      let fCurr := fhsWireFlag (R := R) (m_reg := m_reg) ⟨k', by omega⟩
      have hfCurr_not_mid : ¬ (R * m_reg + R ≤ fCurr.1 ∧ fCurr.1 < R * m_reg + R + (k' + 1)) := by
        dsimp [fCurr, fhsWireFlag]; omega
      have hpNext_not_mid : ¬ (R * m_reg + R ≤ pNext.1 ∧ pNext.1 < R * m_reg + R + (k' + 1)) := by
        dsimp [pNext, fhsWirePref]; omega
      have hz0_fCurr : z0 fCurr = f ⟨k', by omega⟩ := by
        have heq : fCurr = Fin.castAdd (2 * R) (Fin.natAdd (R * m_reg) ⟨k', by omega⟩) := by
          apply Fin.ext; simp [fCurr, fhsWireFlag]
        dsimp only [z0]; rw [heq, Fin.append_left, Fin.append_right]
      have hz0_pNext : z0 pNext = false := by
        have heq : pNext = Fin.natAdd ((R * m_reg) + R) ⟨k' + 1, by omega⟩ := by
          apply Fin.ext; simp [pNext, fhsWirePref]
        dsimp only [z0]; rw [heq, Fin.append_right]
      have hpf : pCurr ≠ fCurr := by
        intro h; have := congrArg Fin.val h; dsimp [pCurr, fCurr, fhsWirePref, fhsWireFlag] at this; omega
      have hfn : fCurr ≠ pNext := by
        intro h; have := congrArg Fin.val h; dsimp [fCurr, pNext, fhsWireFlag, fhsWirePref] at this; omega
      have hpn : pCurr ≠ pNext := fun h => by
        have := congrArg Fin.val (fhsWirePref_inj h); dsimp at this; omega
      by_cases hw_f : w = fCurr
      · subst hw_f
        rw [Function.update_self]
        have hnot : ¬ (R * m_reg + R ≤ fCurr.1 ∧ fCurr.1 < R * m_reg + R + (k' + 2)) := by
          dsimp [fCurr, fhsWireFlag]; omega
        rw [dif_neg hnot, Function.update_of_ne hfn, Function.update_self, Bool.not_not]
        dsimp only [zMid]; exact dif_neg hfCurr_not_mid
      · rw [Function.update_of_ne hw_f]
        by_cases hw_n : w = pNext
        · subst hw_n
          rw [Function.update_self]
          have hpos : R * m_reg + R ≤ pNext.1 ∧ pNext.1 < R * m_reg + R + (k' + 2) := by
            dsimp [pNext, fhsWirePref]; omega
          rw [dif_pos hpos, Function.update_of_ne hfn.symm, Function.update_of_ne hpf,
            Function.update_self]
          have hzMid_pNext : zMid pNext = false := by
            dsimp only [zMid]; rw [dif_neg hpNext_not_mid, hz0_pNext]
          have hzMid_fCurr : zMid fCurr = f ⟨k', by omega⟩ := by
            dsimp only [zMid]; rw [dif_neg hfCurr_not_mid, hz0_fCurr]
          have hzMid_pCurr : zMid pCurr = decide (∀ t : Fin R, t.1 < k' → f t = false) := by
            dsimp only [zMid]
            rw [dif_pos (by dsimp [pCurr, fhsWirePref]; omega)]
            simp [pCurr, fhsWirePref]
          change xor (zMid pNext) (zMid pCurr && !zMid fCurr) = _
          rw [hzMid_pNext, hzMid_fCurr, hzMid_pCurr, Bool.false_xor]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
          have hsub : (fhsWirePref (R := R) (m_reg := m_reg) ⟨k' + 1, hk⟩).1 - (R * m_reg + R) =
              k' + 1 := by
            dsimp [fhsWirePref]; omega
          dsimp only [pNext] at *
          rw [hsub]
          constructor
          · rintro ⟨hprev, hfk⟩ t ht
            by_cases htk : t.1 < k'
            · exact hprev t htk
            · have hteq : t = ⟨k', by omega⟩ := by apply Fin.ext; dsimp; omega
              rwa [hteq]
          · intro hall
            exact ⟨fun t ht => hall t (by omega), hall ⟨k', by omega⟩ (by dsimp; omega)⟩
        · rw [Function.update_of_ne hw_n, Function.update_of_ne hw_f]
          dsimp only [zMid]
          by_cases hw_in : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + (k' + 1)
          · have hw_in' : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + (k' + 2) := by omega
            rw [dif_pos hw_in, dif_pos hw_in']
          · have hw_out' : ¬ (R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + (k' + 2)) := by
              intro h; apply hw_n; apply Fin.ext; dsimp [pNext, fhsWirePref]; omega
            rw [dif_neg hw_in, dif_neg hw_out']

private noncomputable def fhsHitLoop (R m_reg : ℕ) (hR : 1 ≤ R) :
    (k : ℕ) → k ≤ R → LayeredCircuit ((R * m_reg) + R + 2 * R)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk =>
    let prev := fhsHitLoop R m_reg hR k (by omega)
    let j : Fin R := ⟨k, hk⟩
    have hpf : fhsWirePref (R := R) (m_reg := m_reg) j ≠ fhsWireFlag j := by
      intro h; have := congrArg Fin.val h; dsimp [fhsWirePref, fhsWireFlag] at this; omega
    have hph : fhsWirePref (R := R) (m_reg := m_reg) j ≠ fhsWireHit j := by
      intro h; have := congrArg Fin.val h; dsimp [fhsWirePref, fhsWireHit] at this; omega
    have hfh : fhsWireFlag (R := R) (m_reg := m_reg) j ≠ fhsWireHit j := by
      intro h; have := congrArg Fin.val h; dsimp [fhsWireFlag, fhsWireHit] at this; omega
    prev.seq (toffoliOn (fhsWirePref j) (fhsWireFlag j) (fhsWireHit j) hpf hph hfh)

private lemma fhsHitLoop_size (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R) :
    (fhsHitLoop R m_reg hR k hk).size = 5 * k := by
  induction k with
  | zero => simp [fhsHitLoop]
  | succ k ih =>
    simp [fhsHitLoop, ih (by omega)]; omega

private lemma fhsHitLoop_act (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R)
    (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    let z0 : Qubits ((R * m_reg) + R + 2 * R) :=
      Fin.append (Fin.append (flatReg R m_reg blocks) f) (fun _ : Fin (2 * R) => false)
    let z1 : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if _ : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + R then
        decide (∀ t : Fin R, t.1 < w.1 - (R * m_reg + R) → f t = false)
      else z0 w
    let z2 : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if _ : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + k then
        decide (w.1 - (R * m_reg + 2 * R) = firstTrue53Aux R f)
      else z1 w
    act (fhsHitLoop R m_reg hR k hk).unitary (ket z1) = ket z2 := by
  intro z0 z1
  induction k with
  | zero =>
    simp only [fhsHitLoop, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w; rw [dif_neg (by omega)]
  | succ k ih =>
    have hk' : k ≤ R := by omega
    let z2_prev : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if h : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + k then
        decide (w.1 - (R * m_reg + 2 * R) = firstTrue53Aux R f)
      else z1 w
    have hih : act (fhsHitLoop R m_reg hR k hk').unitary (ket z1) = ket z2_prev := ih hk'
    dsimp only [fhsHitLoop]
    rw [LayeredCircuit.seq_unitary, act_mul, hih, act_toffoliOn_ket]
    congr 1; funext w
    let j : Fin R := ⟨k, hk⟩
    by_cases hw : w = fhsWireHit (R := R) (m_reg := m_reg) j
    · subst hw
      rw [Function.update_self, dif_pos (by dsimp [j, fhsWireHit]; omega)]
      have hw_not_prev : ¬ (R * m_reg + 2 * R ≤ (fhsWireHit (R := R) (m_reg := m_reg) j).1 ∧
          (fhsWireHit (R := R) (m_reg := m_reg) j).1 < R * m_reg + 2 * R + k) := by
        dsimp [j, fhsWireHit]; omega
      have hp_not_prev : ¬ (R * m_reg + 2 * R ≤ (fhsWirePref (R := R) (m_reg := m_reg) j).1 ∧
          (fhsWirePref (R := R) (m_reg := m_reg) j).1 < R * m_reg + 2 * R + k) := by
        dsimp [j, fhsWirePref]; omega
      have hf_not_prev : ¬ (R * m_reg + 2 * R ≤ (fhsWireFlag (R := R) (m_reg := m_reg) j).1 ∧
          (fhsWireFlag (R := R) (m_reg := m_reg) j).1 < R * m_reg + 2 * R + k) := by
        dsimp [j, fhsWireFlag]; omega
      have hw_not_pref : ¬ (R * m_reg + R ≤ (fhsWireHit (R := R) (m_reg := m_reg) j).1 ∧
          (fhsWireHit (R := R) (m_reg := m_reg) j).1 < R * m_reg + R + R) := by
        dsimp [j, fhsWireHit]; omega
      have hf_not_pref : ¬ (R * m_reg + R ≤ (fhsWireFlag (R := R) (m_reg := m_reg) j).1 ∧
          (fhsWireFlag (R := R) (m_reg := m_reg) j).1 < R * m_reg + R + R) := by
        dsimp [j, fhsWireFlag]; omega
      have hz0_w : z0 (fhsWireHit (R := R) (m_reg := m_reg) j) = false := by
        have hlt_R : R + k < 2 * R := by omega
        have heq : fhsWireHit (R := R) (m_reg := m_reg) j =
            Fin.natAdd ((R * m_reg) + R) ⟨R + k, hlt_R⟩ := by
          apply Fin.ext; simp [j, fhsWireHit]; omega
        dsimp only [z0]; rw [heq, Fin.append_right]
      have hz0_f : z0 (fhsWireFlag (R := R) (m_reg := m_reg) j) = f j := by
        have heq : fhsWireFlag (R := R) (m_reg := m_reg) j =
            Fin.castAdd (2 * R) (Fin.natAdd (R * m_reg) j) := by
          apply Fin.ext; simp [fhsWireFlag]
        dsimp only [z0]; rw [heq, Fin.append_left, Fin.append_right]
      have hz1_p : z1 (fhsWirePref (R := R) (m_reg := m_reg) j) =
          decide (∀ t : Fin R, t.1 < k → f t = false) := by
        dsimp only [z1]
        rw [dif_pos (by dsimp [j, fhsWirePref]; omega)]
        simp [j, fhsWirePref]
      have hz2_w : z2_prev (fhsWireHit (R := R) (m_reg := m_reg) j) = false := by
        dsimp only [z2_prev]; rw [dif_neg hw_not_prev]
        dsimp only [z1]; rw [dif_neg hw_not_pref, hz0_w]
      have hz2_p : z2_prev (fhsWirePref (R := R) (m_reg := m_reg) j) =
          decide (∀ t : Fin R, t.1 < k → f t = false) := by
        dsimp only [z2_prev]; rw [dif_neg hp_not_prev, hz1_p]
      have hz2_f : z2_prev (fhsWireFlag (R := R) (m_reg := m_reg) j) = f j := by
        dsimp only [z2_prev]; rw [dif_neg hf_not_prev]
        dsimp only [z1]; rw [dif_neg hf_not_pref, hz0_f]
      change xor (z2_prev (fhsWireHit j)) (z2_prev (fhsWirePref j) && z2_prev (fhsWireFlag j)) = _
      rw [hz2_w, hz2_p, hz2_f, Bool.false_xor]
      have hsub : (fhsWireHit (R := R) (m_reg := m_reg) j).1 - (R * m_reg + 2 * R) = j.1 := by
        dsimp [j, fhsWireHit]; omega
      rw [hsub]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      rw [firstTrue53Aux_eq_iff f j]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    · rw [Function.update_of_ne hw]
      dsimp only [z2_prev]
      by_cases hw_in : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + k
      · have hw_in' : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + (k + 1) := by omega
        rw [dif_pos hw_in, dif_pos hw_in']
      · have hw_out' : ¬ (R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + (k + 1)) := by
          intro h; apply hw; apply Fin.ext; dsimp [j, fhsWireHit]; omega
        rw [dif_neg hw_in, dif_neg hw_out']

private noncomputable def fhsPrefixCompute (R m_reg : ℕ) (hR : 1 ≤ R) :
    LayeredCircuit ((R * m_reg) + R + 2 * R) :=
  (fhsPrefPrefix R m_reg hR R le_rfl).seq (fhsHitLoop R m_reg hR R le_rfl)

private lemma fhsPrefixCompute_size (R m_reg : ℕ) (hR : 1 ≤ R) :
    (fhsPrefixCompute R m_reg hR).size ≤ 12 * R := by
  rw [fhsPrefixCompute, LayeredCircuit.seq_size]
  have h1 := fhsPrefPrefix_size R m_reg hR R le_rfl
  have h2 := fhsHitLoop_size R m_reg hR R le_rfl
  omega

private def packFHS {R m_reg : ℕ} (bl : Fin R → Qubits m_reg) (rest : Fin (R + 2 * R) → Bool) :
    Qubits ((R * m_reg) + R + 2 * R) :=
  fun w => if h : w.1 < R * m_reg then flatReg R m_reg bl ⟨w.1, h⟩
    else rest ⟨w.1 - R * m_reg, by have := w.isLt; omega⟩

private lemma packFHS_block {R m_reg : ℕ} (bl : Fin R → Qubits m_reg)
    (rest : Fin (R + 2 * R) → Bool) (i : Fin R) (b : Fin m_reg) :
    packFHS bl rest (fhsWireBlock i b) = bl i b := by
  have hlt : (fhsWireBlock (R := R) (m_reg := m_reg) i b).1 < R * m_reg := fin_prod_lt i b
  dsimp only [packFHS]
  rw [dif_pos hlt]
  have heq : (⟨(fhsWireBlock (R := R) (m_reg := m_reg) i b).1, hlt⟩ : Fin (R * m_reg)) =
      finProdFinEquiv (i, b) := by
    apply Fin.ext; simp only [fhsWireBlock, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk]; ring
  rw [heq]
  exact congrFun (congrArg (fun fn => fn i) (splitReg_flatReg R m_reg bl)) b

private lemma packFHS_rest {R m_reg : ℕ} (bl : Fin R → Qubits m_reg)
    (rest : Fin (R + 2 * R) → Bool) (w : Fin ((R * m_reg) + R + 2 * R)) (hw : ¬ w.1 < R * m_reg) :
    packFHS bl rest w = rest ⟨w.1 - R * m_reg, by have := w.isLt; omega⟩ := by
  dsimp only [packFHS]; rw [dif_neg hw]

private lemma packFHS_hit {R m_reg : ℕ} (bl : Fin R → Qubits m_reg)
    (rest : Fin (R + 2 * R) → Bool) (j : Fin R) :
    packFHS bl rest (fhsWireHit j) = rest ⟨2 * R + j.1, by have := j.isLt; omega⟩ := by
  have hnot : ¬ (fhsWireHit (R := R) (m_reg := m_reg) j).1 < R * m_reg := by
    dsimp [fhsWireHit]; omega
  rw [packFHS_rest bl rest _ hnot]
  congr 1; apply Fin.ext; simp [fhsWireHit]; omega

private lemma packFHS_zero {R m_reg : ℕ} (bl : Fin R → Qubits m_reg) (f : Qubits R) :
    packFHS bl (Fin.append f (fun _ : Fin (2 * R) => false)) =
      Fin.append (Fin.append (flatReg R m_reg bl) f) (fun _ : Fin (2 * R) => false) := by
  funext w
  dsimp only [packFHS]
  by_cases hw : w.1 < R * m_reg
  · rw [dif_pos hw]
    have h1 : w = Fin.castAdd (2 * R) (Fin.castAdd R ⟨w.1, hw⟩) := Fin.ext rfl
    conv_rhs => rw [h1, Fin.append_left, Fin.append_left]
  · rw [dif_neg hw]
    by_cases hw2 : w.1 < R * m_reg + R
    · have h1 : w = Fin.castAdd (2 * R) (Fin.natAdd (R * m_reg) ⟨w.1 - R * m_reg, by omega⟩) := by
        apply Fin.ext; simp; omega
      have h2 : (⟨w.1 - R * m_reg, by have := w.isLt; omega⟩ : Fin (R + 2 * R)) =
          Fin.castAdd (2 * R) ⟨w.1 - R * m_reg, by omega⟩ := Fin.ext rfl
      rw [h2, Fin.append_left]
      conv_rhs => rw [h1, Fin.append_left, Fin.append_right]
    · have h1 : w = Fin.natAdd ((R * m_reg) + R) ⟨w.1 - (R * m_reg + R), by have := w.isLt; omega⟩ := by
        apply Fin.ext; simp; omega
      have h2 : (⟨w.1 - R * m_reg, by have := w.isLt; omega⟩ : Fin (R + 2 * R)) =
          Fin.natAdd R ⟨w.1 - (R * m_reg + R), by have := w.isLt; omega⟩ := by
        apply Fin.ext; simp; omega
      rw [h2, Fin.append_right]
      conv_rhs => rw [h1, Fin.append_right]

private noncomputable def fhsSwapOneBlock (R m_reg : ℕ) (hR : 1 ≤ R) (j : Fin R) (hj : 1 ≤ j.1) :
    (k : ℕ) → k ≤ m_reg → LayeredCircuit ((R * m_reg) + R + 2 * R)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk =>
    let prev := fhsSwapOneBlock R m_reg hR j hj k (by omega)
    let b : Fin m_reg := ⟨k, hk⟩
    let wC := fhsWireHit (R := R) (m_reg := m_reg) j
    let wA := fhsWireBlock (R := R) (m_reg := m_reg) ⟨0, hR⟩ b
    let wB := fhsWireBlock (R := R) (m_reg := m_reg) j b
    have hca : wC ≠ wA := by
      intro h; have h1 := congrArg Fin.val h; have hlt := fin_prod_lt ⟨0, hR⟩ b
      dsimp only [wC, wA, fhsWireHit, fhsWireBlock] at h1; omega
    have hcb : wC ≠ wB := by
      intro h; have h1 := congrArg Fin.val h; have hlt := fin_prod_lt j b
      dsimp only [wC, wB, fhsWireHit, fhsWireBlock] at h1; omega
    have hab : wA ≠ wB := fun h => by
      have h0 := (fhsWireBlock_inj h).1
      have h1 := congrArg Fin.val h0
      simp at h1; omega
    prev.seq (cswapOn wC wA wB hca hcb hab)

private lemma fhsSwapOneBlock_size (R m_reg : ℕ) (hR : 1 ≤ R) (j : Fin R) (hj : 1 ≤ j.1)
    (k : ℕ) (hk : k ≤ m_reg) :
    (fhsSwapOneBlock R m_reg hR j hj k hk).size = 7 * k := by
  induction k with
  | zero => simp [fhsSwapOneBlock]
  | succ k ih =>
    simp [fhsSwapOneBlock, ih (by omega)]; omega

private lemma fhsSwapOneBlock_act (R m_reg : ℕ) (hR : 1 ≤ R) (j : Fin R) (hj : 1 ≤ j.1)
    (k : ℕ) (hk : k ≤ m_reg) (z : Qubits ((R * m_reg) + R + 2 * R)) :
    let z' : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if z (fhsWireHit j) then
        if h : w.1 < k then
          z (fhsWireBlock j ⟨w.1, lt_of_lt_of_le h hk⟩)
        else if h : j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + k then
          z (fhsWireBlock ⟨0, hR⟩ ⟨w.1 - j.1 * m_reg, by omega⟩)
        else z w
      else z w
    act (fhsSwapOneBlock R m_reg hR j hj k hk).unitary (ket z) = ket z' := by
  induction k with
  | zero =>
    simp only [fhsSwapOneBlock, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w
    split_ifs with hzc hlt hbd
    · omega
    · omega
    · rfl
    · rfl
  | succ k ih =>
    have hk' : k ≤ m_reg := by omega
    let b : Fin m_reg := ⟨k, hk⟩
    let zMid : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
      if z (fhsWireHit j) then
        if h : w.1 < k then
          z (fhsWireBlock j ⟨w.1, lt_of_lt_of_le h hk'⟩)
        else if h : j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + k then
          z (fhsWireBlock ⟨0, hR⟩ ⟨w.1 - j.1 * m_reg, by omega⟩)
        else z w
      else z w
    have hih : act (fhsSwapOneBlock R m_reg hR j hj k hk').unitary (ket z) = ket zMid := ih hk'
    dsimp only [fhsSwapOneBlock]
    rw [LayeredCircuit.seq_unitary, act_mul, hih, act_cswapOn_ket]
    congr 1
    let wC := fhsWireHit (R := R) (m_reg := m_reg) j
    let wA := fhsWireBlock (R := R) (m_reg := m_reg) ⟨0, hR⟩ b
    let wB := fhsWireBlock (R := R) (m_reg := m_reg) j b
    have hmR : m_reg ≤ R * m_reg := Nat.le_mul_of_pos_left m_reg hR
    have hmj : m_reg ≤ j.1 * m_reg := Nat.le_mul_of_pos_left m_reg hj
    have hC_lt : ¬ wC.1 < k := by
      dsimp only [wC, fhsWireHit]; omega
    have hC_bd : ¬ (j.1 * m_reg ≤ wC.1 ∧ wC.1 < j.1 * m_reg + k) := by
      have hlt := fin_prod_lt j b
      dsimp only [wC, fhsWireHit, b] at hlt ⊢; omega
    have hzMid_C : zMid wC = z wC := by
      dsimp only [zMid]; rw [dif_neg hC_lt, dif_neg hC_bd]; simp
    have hA_val : wA.1 = k := by simp [wA, fhsWireBlock, b]
    have hB_val : wB.1 = j.1 * m_reg + k := by simp [wB, fhsWireBlock, b]
    have hA_lt : ¬ wA.1 < k := by omega
    have hA_bd : ¬ (j.1 * m_reg ≤ wA.1 ∧ wA.1 < j.1 * m_reg + k) := by omega
    have hzMid_A : zMid wA = z wA := by
      dsimp only [zMid]; rw [dif_neg hA_lt, dif_neg hA_bd]; simp
    have hB_lt : ¬ wB.1 < k := by omega
    have hB_bd : ¬ (j.1 * m_reg ≤ wB.1 ∧ wB.1 < j.1 * m_reg + k) := by omega
    have hzMid_B : zMid wB = z wB := by
      dsimp only [zMid]; rw [dif_neg hB_lt, dif_neg hB_bd]; simp
    rw [hzMid_C]
    funext w
    by_cases hzc : z wC = true
    · have hzc' : z (fhsWireHit j) = true := hzc
      rw [if_pos hzc, if_pos hzc']
      by_cases hwa : w = wA
      · subst hwa
        rw [if_pos rfl, hzMid_B, dif_pos (by omega)]
        congr 1; apply Fin.ext; simp [wB, fhsWireBlock, b, hA_val]
      · rw [if_neg hwa]
        by_cases hwb : w = wB
        · subst hwb
          rw [if_pos rfl, hzMid_A]
          rw [dif_neg (by omega), dif_pos (by omega)]
          congr 1; apply Fin.ext; simp [wA, fhsWireBlock, b, hB_val]
        · rw [if_neg hwb]
          have hne_k : w.1 ≠ k := fun h => hwa (Fin.ext (by rw [hA_val, h]))
          have hne_jk : w.1 ≠ j.1 * m_reg + k := fun h => hwb (Fin.ext (by rw [hB_val, h]))
          dsimp only [zMid]
          rw [if_pos hzc']
          by_cases h1 : w.1 < k
          · have h1' : w.1 < k + 1 := by omega
            rw [dif_pos h1, dif_pos h1']
          · have h1' : ¬ w.1 < k + 1 := by omega
            rw [dif_neg h1, dif_neg h1']
            by_cases h2 : j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + k
            · have h2' : j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + (k + 1) := by omega
              rw [dif_pos h2, dif_pos h2']
            · have h2' : ¬ (j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + (k + 1)) := by omega
              rw [dif_neg h2, dif_neg h2']
    · have hzf : z wC = false := Bool.eq_false_iff.mpr hzc
      have hzf' : z (fhsWireHit j) = false := hzf
      dsimp only [zMid]
      simp [hzf, hzf']

private lemma fhsSwapOneBlock_swap (R m_reg : ℕ) (hR : 1 ≤ R) (j : Fin R) (hj : 1 ≤ j.1)
    (blocks : Fin R → Qubits m_reg) (rest : Fin (R + 2 * R) → Bool)
    (hHit : rest ⟨2 * R + j.1, by have := j.isLt; omega⟩ = true) :
    act (fhsSwapOneBlock R m_reg hR j hj m_reg le_rfl).unitary (ket (packFHS blocks rest)) =
      ket (packFHS (fun i => blocks (Equiv.swap ⟨0, hR⟩ j i)) rest) := by
  rw [fhsSwapOneBlock_act R m_reg hR j hj m_reg le_rfl (packFHS blocks rest)]
  congr 1
  have hzc : packFHS blocks rest (fhsWireHit j) = true := by
    rw [packFHS_hit, hHit]
  funext w
  rw [if_pos hzc]
  by_cases hw : w.1 < R * m_reg
  · set p := finProdFinEquiv.symm ⟨w.1, hw⟩
    have hw_eq : w = fhsWireBlock p.1 p.2 := by
      apply Fin.ext
      dsimp [fhsWireBlock]
      have h1 := congrArg Fin.val (finProdFinEquiv.apply_symm_apply ⟨w.1, hw⟩)
      simp only [finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_mk] at h1
      change p.2.1 + m_reg * p.1.1 = w.1 at h1
      rw [Nat.mul_comm] at h1; omega
    have hw_val : w.1 = p.1.1 * m_reg + p.2.1 := by
      rw [hw_eq]; rfl
    rw [hw_eq, packFHS_block]
    by_cases hp0 : p.1 = ⟨0, hR⟩
    · have hlt_m : (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 < m_reg := by
        dsimp [fhsWireBlock]; rw [hp0]; simp [p.2.isLt]
      rw [dif_pos hlt_m]
      have hb_eq : (⟨(fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1, hlt_m⟩ : Fin m_reg) = p.2 := by
        apply Fin.ext; dsimp [fhsWireBlock]; rw [hp0]; simp
      rw [hb_eq, packFHS_block, packFHS_block, hp0, Equiv.swap_apply_left]
    · have hnot_m : ¬ (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 < m_reg := by
        dsimp [fhsWireBlock]
        have hp_ge : 1 ≤ p.1.1 := Nat.pos_of_ne_zero fun h0 => hp0 (Fin.ext h0)
        nlinarith
      rw [dif_neg hnot_m]
      by_cases hpj : p.1 = j
      · have hbd : j.1 * m_reg ≤ (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 ∧
            (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 < j.1 * m_reg + m_reg := by
          dsimp [fhsWireBlock]; rw [hpj]; exact ⟨by omega, by have := p.2.isLt; omega⟩
        rw [dif_pos hbd]
        have hb_eq : (⟨(fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 - j.1 * m_reg,
            by omega⟩ : Fin m_reg) = p.2 := by
          apply Fin.ext; dsimp [fhsWireBlock]; rw [hpj]; simp
        rw [hb_eq, packFHS_block, packFHS_block, hpj, Equiv.swap_apply_right]
      · have hnot_bd : ¬ (j.1 * m_reg ≤ (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 ∧
            (fhsWireBlock (R := R) (m_reg := m_reg) p.1 p.2).1 < j.1 * m_reg + m_reg) := by
          dsimp [fhsWireBlock]
          have hne_val : p.1.1 ≠ j.1 := fun h => hpj (Fin.ext h)
          have hlt_p := p.2.isLt
          rcases lt_or_gt_of_ne hne_val with hlt | hgt
          · have : p.1.1 + 1 ≤ j.1 := hlt
            have : (p.1.1 + 1) * m_reg ≤ j.1 * m_reg := Nat.mul_le_mul_right _ this
            rw [Nat.add_mul, one_mul] at this; omega
          · have : j.1 + 1 ≤ p.1.1 := hgt
            have : (j.1 + 1) * m_reg ≤ p.1.1 * m_reg := Nat.mul_le_mul_right _ this
            rw [Nat.add_mul, one_mul] at this; omega
        rw [dif_neg hnot_bd, packFHS_block, Equiv.swap_apply_of_ne_of_ne hp0 hpj]
  · have hnot_m : ¬ w.1 < m_reg := by
      intro h; apply hw
      calc w.1 < m_reg := h
        _ = 1 * m_reg := (one_mul _).symm
        _ ≤ R * m_reg := Nat.mul_le_mul_right _ hR
    have hnot_bd : ¬ (j.1 * m_reg ≤ w.1 ∧ w.1 < j.1 * m_reg + m_reg) := by
      intro h; apply hw
      have h1 : j.1 + 1 ≤ R := j.isLt
      have h2 : (j.1 + 1) * m_reg ≤ R * m_reg := Nat.mul_le_mul_right _ h1
      linarith
    rw [dif_neg hnot_m, dif_neg hnot_bd, packFHS_rest _ _ _ hw, packFHS_rest _ _ _ hw]

private lemma fhsSwapOneBlock_id (R m_reg : ℕ) (hR : 1 ≤ R) (j : Fin R) (hj : 1 ≤ j.1)
    (z : Qubits ((R * m_reg) + R + 2 * R)) (hHit : z (fhsWireHit j) = false) :
    act (fhsSwapOneBlock R m_reg hR j hj m_reg le_rfl).unitary (ket z) = ket z := by
  rw [fhsSwapOneBlock_act]
  congr 1; funext w; simp [hHit]

private noncomputable def fhsSwapStage (R m_reg : ℕ) (hR : 1 ≤ R) :
    (k : ℕ) → k ≤ R → LayeredCircuit ((R * m_reg) + R + 2 * R)
  | 0, _ => LayeredCircuit.id _
  | k + 1, hk =>
    if h1 : 1 ≤ k then
      (fhsSwapStage R m_reg hR k (by omega)).seq
        (fhsSwapOneBlock R m_reg hR ⟨k, hk⟩ h1 m_reg le_rfl)
    else
      LayeredCircuit.id _

private lemma fhsSwapStage_size (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R) :
    (fhsSwapStage R m_reg hR k hk).size ≤ 7 * (k - 1) * m_reg := by
  induction k with
  | zero => simp [fhsSwapStage]
  | succ k ih =>
    dsimp only [fhsSwapStage]
    split_ifs with h1
    · have hih := ih (by omega)
      rw [LayeredCircuit.seq_size, fhsSwapOneBlock_size]
      have hmul : 7 * (k - 1) * m_reg + 7 * m_reg = 7 * (k + 1 - 1) * m_reg := by
        cases k with
        | zero => omega
        | succ k' => simp only [Nat.add_sub_cancel]; ring
      omega
    · simp

private lemma fhsSwapStage_act (R m_reg : ℕ) (hR : 1 ≤ R) (k : ℕ) (hk : k ≤ R)
    (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    let rest : Fin (R + 2 * R) → Bool := fun w =>
      if h : R ≤ w.1 ∧ w.1 < 2 * R then
        decide (∀ t : Fin R, t.1 < w.1 - R → f t = false)
      else if h : 2 * R ≤ w.1 ∧ w.1 < 3 * R then
        decide (w.1 - 2 * R = firstTrue53Aux R f)
      else f ⟨w.1, by omega⟩
    let blocksOut : Fin R → Qubits m_reg :=
      if h : ∃ j : Fin R, f j = true ∧ firstTrue53Aux R f < k then
        fun i => blocks (Equiv.swap ⟨0, hR⟩ (firstTrue53 f ⟨h.choose, h.choose_spec.1⟩) i)
      else blocks
    act (fhsSwapStage R m_reg hR k hk).unitary (ket (packFHS blocks rest)) =
      ket (packFHS blocksOut rest) := by
  intro rest
  induction k with
  | zero =>
    simp only [fhsSwapStage, LayeredCircuit.id_unitary, act_one]
    congr 2; rw [dif_neg (by rintro ⟨_, _, h⟩; omega)]
  | succ k ih =>
    dsimp only [fhsSwapStage]
    by_cases h1 : 1 ≤ k
    · rw [dif_pos h1, LayeredCircuit.seq_unitary, act_mul, ih (by omega)]
      let j : Fin R := ⟨k, hk⟩
      by_cases hhit : k = firstTrue53Aux R f
      · have hj_spec := (firstTrue53Aux_eq_iff f j).mp hhit
        have hnot_prev : ¬ ∃ j' : Fin R, f j' = true ∧ firstTrue53Aux R f < k := by
          rintro ⟨_, _, hlt⟩; omega
        rw [dif_neg hnot_prev]
        have hHit_true : rest ⟨2 * R + j.1, by have := j.isLt; omega⟩ = true := by
          dsimp only [rest]
          rw [dif_neg (by dsimp [j]; omega), dif_pos (by dsimp [j]; omega)]
          simp [j, hhit]
        have hsw := fhsSwapOneBlock_swap R m_reg hR j h1 blocks rest hHit_true
        rw [hsw]
        congr 2
        have hex : ∃ j' : Fin R, f j' = true ∧ firstTrue53Aux R f < k + 1 :=
          ⟨j, hj_spec.1, by omega⟩
        rw [dif_pos hex]
        have hft : firstTrue53 f ⟨hex.choose, hex.choose_spec.1⟩ = j := by
          apply Fin.ext; exact hhit.symm
        rw [hft]
      · have hHit_false : ∀ bl : Fin R → Qubits m_reg,
            packFHS bl rest (fhsWireHit j) = false := fun bl => by
          rw [packFHS_hit]
          dsimp only [rest]
          rw [dif_neg (by dsimp [j]; omega), dif_pos (by dsimp [j]; omega)]
          simp [j, hhit]
        rw [fhsSwapOneBlock_id R m_reg hR j h1 _ (hHit_false _)]
        congr 2
        by_cases hprev : ∃ j' : Fin R, f j' = true ∧ firstTrue53Aux R f < k
        · have hnext : ∃ j' : Fin R, f j' = true ∧ firstTrue53Aux R f < k + 1 :=
            ⟨hprev.choose, hprev.choose_spec.1, by omega⟩
          rw [dif_pos hprev, dif_pos hnext]
        · have hnext : ¬ ∃ j' : Fin R, f j' = true ∧ firstTrue53Aux R f < k + 1 := by
            rintro ⟨j', hj', hlt⟩; apply hprev; exact ⟨j', hj', by omega⟩
          rw [dif_neg hprev, dif_neg hnext]
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [dif_neg h1, LayeredCircuit.id_unitary, act_one]
      congr 2
      by_cases hex : ∃ j : Fin R, f j = true ∧ firstTrue53Aux R f < 0 + 1
      · rw [dif_pos hex]
        have h0 : firstTrue53 f ⟨hex.choose, hex.choose_spec.1⟩ = ⟨0, hR⟩ := by
          apply Fin.ext
          have := hex.choose_spec.2
          change firstTrue53Aux R f = 0; omega
        rw [h0, Equiv.swap_self]
        rfl
      · rw [dif_neg hex]

noncomputable def firstHitSwapCircuit (R m_reg : ℕ) : Circuit gates12 ((R * m_reg) + R + 2 * R) :=
  if hR : 1 ≤ R then
    let pref := fhsPrefixCompute R m_reg hR
    let sw := fhsSwapStage R m_reg hR R le_rfl
    (pref.seq (sw.seq pref.adj)).toCircuit
  else
    []

lemma firstHitSwapCircuit_size (R m_reg : ℕ) :
    (firstHitSwapCircuit R m_reg).length ≤ 24 * R * (m_reg + 1) := by
  unfold firstHitSwapCircuit
  split_ifs with hR
  · change (_ : LayeredCircuit _).size ≤ _
    simp only [LayeredCircuit.seq_size, LayeredCircuit.adj_size]
    have h1 := fhsPrefixCompute_size R m_reg hR
    have h2 := fhsSwapStage_size R m_reg hR R le_rfl
    have hmul : 7 * (R - 1) * m_reg ≤ 7 * R * m_reg := by
      have : R - 1 ≤ R := by omega
      gcongr
    have hRmul : 24 * R + 7 * R * m_reg ≤ 24 * R * (m_reg + 1) := by nlinarith
    omega
  · simp

lemma firstHitSwapCircuit_act (R m_reg : ℕ) (blocks : Fin R → Qubits m_reg) (f : Qubits R) :
    act (firstHitSwapCircuit R m_reg).unitary
        (ket (Fin.append (Fin.append (flatReg R m_reg blocks) f) (fun _ : Fin (2 * R) => false))) =
      ket (Fin.append (Fin.append (flatReg R m_reg (swappedBlocks53 blocks f)) f)
        (fun _ : Fin (2 * R) => false)) := by
  by_cases hR : 1 ≤ R
  · simp only [firstHitSwapCircuit, dif_pos hR]
    let rest0 : Fin (R + 2 * R) → Bool := Fin.append f (fun _ : Fin (2 * R) => false)
    let rest1 : Fin (R + 2 * R) → Bool := fun w =>
      if h : R ≤ w.1 ∧ w.1 < 2 * R then
        decide (∀ t : Fin R, t.1 < w.1 - R → f t = false)
      else if h : 2 * R ≤ w.1 ∧ w.1 < 3 * R then
        decide (w.1 - 2 * R = firstTrue53Aux R f)
      else f ⟨w.1, by omega⟩
    have hpref_act : ∀ bl : Fin R → Qubits m_reg,
        act (fhsPrefixCompute R m_reg hR).unitary (ket (packFHS bl rest0)) =
          ket (packFHS bl rest1) := by
      intro bl
      let z0 := Fin.append (Fin.append (flatReg R m_reg bl) f) (fun _ : Fin (2 * R) => false)
      let z1 : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
        if h : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + R then
          decide (∀ t : Fin R, t.1 < w.1 - (R * m_reg + R) → f t = false)
        else z0 w
      let z2 : Qubits ((R * m_reg) + R + 2 * R) := fun w =>
        if h : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + R then
          decide (w.1 - (R * m_reg + 2 * R) = firstTrue53Aux R f)
        else z1 w
      have h1 : act (fhsPrefPrefix R m_reg hR R le_rfl).unitary (ket z0) = ket z1 :=
        fhsPrefPrefix_act R m_reg hR R le_rfl bl f
      have h2 : act (fhsHitLoop R m_reg hR R le_rfl).unitary (ket z1) = ket z2 :=
        fhsHitLoop_act R m_reg hR R le_rfl bl f
      dsimp only [fhsPrefixCompute]
      rw [LayeredCircuit.seq_unitary, act_mul, packFHS_zero, h1, h2]
      congr 1; funext w
      dsimp only [z2, z1, packFHS, rest1]
      by_cases hw : w.1 < R * m_reg
      · have h1_not : ¬ (R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + R) := by omega
        have h2_not : ¬ (R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + R) := by omega
        rw [dif_neg h2_not, dif_neg h1_not, dif_pos hw]
        have hw_cast : w = Fin.castAdd (2 * R) (Fin.castAdd R ⟨w.1, hw⟩) := Fin.ext rfl
        conv_lhs => dsimp only [z0]; rw [hw_cast, Fin.append_left, Fin.append_left]
      · rw [dif_neg hw]
        by_cases h2w : R * m_reg + 2 * R ≤ w.1 ∧ w.1 < R * m_reg + 2 * R + R
        · have h2r : 2 * R ≤ w.1 - R * m_reg ∧ w.1 - R * m_reg < 3 * R := by omega
          have h1r : ¬ (R ≤ w.1 - R * m_reg ∧ w.1 - R * m_reg < 2 * R) := by omega
          rw [dif_pos h2w, dif_neg h1r, dif_pos h2r]
          congr 2; omega
        · rw [dif_neg h2w]
          by_cases h1w : R * m_reg + R ≤ w.1 ∧ w.1 < R * m_reg + R + R
          · have h1r : R ≤ w.1 - R * m_reg ∧ w.1 - R * m_reg < 2 * R := by omega
            rw [dif_pos h1w, dif_pos h1r]
            have hsub : w.1 - (R * m_reg + R) = w.1 - R * m_reg - R := by omega
            simp only [hsub]
          · rw [dif_neg h1w]
            have hw_ltR : w.1 - R * m_reg < R := by have := w.isLt; omega
            have h1r : ¬ (R ≤ w.1 - R * m_reg ∧ w.1 - R * m_reg < 2 * R) := by omega
            have h2r : ¬ (2 * R ≤ w.1 - R * m_reg ∧ w.1 - R * m_reg < 3 * R) := by omega
            rw [dif_neg h1r, dif_neg h2r]
            have hw_cast : w = Fin.castAdd (2 * R)
                (Fin.natAdd (R * m_reg) ⟨w.1 - R * m_reg, hw_ltR⟩) := by
              apply Fin.ext; simp; omega
            conv_lhs => dsimp only [z0]; rw [hw_cast, Fin.append_left, Fin.append_right]
    have hsw_act := fhsSwapStage_act R m_reg hR R le_rfl blocks f
    have hsw_eq : (if h : ∃ j : Fin R, f j = true ∧ firstTrue53Aux R f < R then
          fun i => blocks (Equiv.swap ⟨0, hR⟩ (firstTrue53 f ⟨h.choose, h.choose_spec.1⟩) i)
        else blocks) = swappedBlocks53 blocks f := by
      by_cases hex : ∃ j : Fin R, f j = true
      · have hex' : ∃ j : Fin R, f j = true ∧ firstTrue53Aux R f < R :=
          ⟨hex.choose, hex.choose_spec, firstTrue53Aux_lt f hex⟩
        rw [dif_pos hex', swappedBlocks53, dif_pos hex]
      · have hex' : ¬ ∃ j : Fin R, f j = true ∧ firstTrue53Aux R f < R := fun h =>
          hex ⟨h.choose, h.choose_spec.1⟩
        rw [dif_neg hex', swappedBlocks53, dif_neg hex]
    rw [hsw_eq] at hsw_act
    have hadj : act (fhsPrefixCompute R m_reg hR).adj.unitary
        (ket (packFHS (swappedBlocks53 blocks f) rest1)) =
        ket (packFHS (swappedBlocks53 blocks f) rest0) := by
      rw [← hpref_act (swappedBlocks53 blocks f), ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp (fhsPrefixCompute R m_reg hR).unitary_mem_unitaryGroup,
        act_one]
    rw [← packFHS_zero blocks f, ← packFHS_zero (swappedBlocks53 blocks f) f]
    change act ((fhsPrefixCompute R m_reg hR).seq
      ((fhsSwapStage R m_reg hR R le_rfl).seq (fhsPrefixCompute R m_reg hR).adj)).unitary
      (ket (packFHS blocks rest0)) = ket (packFHS (swappedBlocks53 blocks f) rest0)
    simp only [LayeredCircuit.seq_unitary, act_mul]
    rw [hpref_act blocks, hsw_act, hadj]
  · have hR0 : R = 0 := by omega
    subst hR0
    simp only [firstHitSwapCircuit, dif_neg (by decide : ¬ 1 ≤ 0), Circuit.unitary]
    simp only [List.map_nil, List.reverse_nil, List.prod_nil, act_one]
    congr 1

/-! ### 3. Generic `multiEqCtrl1`, `ltConstCircuit`, `rippleAddBits` & `goodFlagCompute` -/

private lemma multiEqCtrl1_pauliX_implements (L : ℕ) (pat : Qubits L) :
    (multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).ImplementsOnClean
      (permMat fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
  have h := multiEqCtrl1_implements L pat pauliX pauliX_mem_unitaryGroup
  have heq : eqCtrlMat L pat pauliX =
      permMat (fun v : Qubits (L + 1) =>
        Function.update v ⟨L, Nat.lt_succ_self L⟩
          (xor (v ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, v ⟨i.1, by omega⟩ = pat i)))) := by
    ext y z
    simp only [eqCtrlMat, permMat, Matrix.of_apply]
    by_cases hyz : ∀ i : Fin L, y ⟨i.1, by omega⟩ = z ⟨i.1, by omega⟩
    · rw [if_pos hyz]
      by_cases hall : ∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i
      · rw [if_pos hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_true hall, Bool.xor_true]
          constructor
          · intro h1; rw [h1, Function.update_self]
          · intro h1; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · have hne : k'.castSucc ≠ ⟨L, Nat.lt_succ_self L⟩ := Fin.ne_of_val_ne (by simp; omega)
              rw [Function.update_of_ne hne]; exact hyz k'
            · have hlast : Fin.last L = ⟨L, Nat.lt_succ_self L⟩ := rfl
              rw [hlast, Function.update_self]; exact h1
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = !z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos (hy_eq.mpr hym), hym]
          cases z ⟨L, Nat.lt_succ_self L⟩ <;> simp [pauliX]
        · rw [if_neg (mt hy_eq.mp hym)]
          cases hzm : z ⟨L, Nat.lt_succ_self L⟩ <;> cases hym' : y ⟨L, Nat.lt_succ_self L⟩ <;>
            simp [pauliX, hzm, hym'] at hym ⊢
      · rw [if_neg hall]
        have hy_eq : (y = Function.update z ⟨L, Nat.lt_succ_self L⟩
            (xor (z ⟨L, Nat.lt_succ_self L⟩) (decide (∀ i : Fin L, z ⟨i.1, by omega⟩ = pat i)))) ↔
            y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩ := by
          simp only [decide_eq_false hall, Bool.xor_false, Function.update_eq_self]
          constructor
          · intro h1; rw [h1]
          · intro h1; funext k
            rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
            · exact hyz k'
            · exact h1
        by_cases hym : y ⟨L, Nat.lt_succ_self L⟩ = z ⟨L, Nat.lt_succ_self L⟩
        · rw [if_pos hym, if_pos (hy_eq.mpr hym)]
        · rw [if_neg hym, if_neg (mt hy_eq.mp hym)]
    · rw [if_neg hyz]
      symm; rw [if_neg]
      intro h1; apply hyz; intro i
      have h2 := congrFun h1 ⟨i.1, by omega⟩
      have hne : (⟨i.1, by omega⟩ : Fin (L + 1)) ≠ ⟨L, Nat.lt_succ_self L⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      rwa [Function.update_of_ne hne] at h2
  rwa [← heq]

private def triEmb {A B W : ℕ}
    (lo : Fin A → Fin W) (mid : Fin W) (hi : Fin B → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin A, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin B, mid.1 < (hi j).1) :
    Fin (A + 1 + B) ↪ Fin W where
  toFun w :=
    if hw : w.1 < A then lo ⟨w.1, hw⟩
    else if _ : w.1 = A then mid
    else hi ⟨w.1 - (A + 1), by have := w.isLt; omega⟩
  inj' u v huv := by
    have hv := congrArg Fin.val huv
    dsimp only at huv hv
    by_cases hu1 : u.1 < A <;> by_cases hv1 : v.1 < A
    · rw [dif_pos hu1, dif_pos hv1] at huv
      exact Fin.ext (by have := congrArg Fin.val (hlo_inj huv); simpa using this)
    · have hlt := hlo_mid ⟨u.1, hu1⟩
      rw [dif_pos hu1, dif_neg hv1] at hv
      by_cases hv2 : v.1 = A
      · rw [dif_pos hv2] at hv; omega
      · rw [dif_neg hv2] at hv
        have hhi := hmid_hi ⟨v.1 - (A + 1), by have := v.isLt; omega⟩
        omega
    · have hlt := hlo_mid ⟨v.1, hv1⟩
      rw [dif_neg hu1, dif_pos hv1] at hv
      by_cases hu2 : u.1 = A
      · rw [dif_pos hu2] at hv; omega
      · rw [dif_neg hu2] at hv
        have hhi := hmid_hi ⟨u.1 - (A + 1), by have := u.isLt; omega⟩
        omega
    · rw [dif_neg hu1, dif_neg hv1] at huv hv
      by_cases hu2 : u.1 = A <;> by_cases hv2 : v.1 = A
      · exact Fin.ext (by omega)
      · rw [dif_pos hu2, dif_neg hv2] at hv
        have hhi := hmid_hi ⟨v.1 - (A + 1), by have := v.isLt; omega⟩
        omega
      · rw [dif_neg hu2, dif_pos hv2] at hv
        have hhi := hmid_hi ⟨u.1 - (A + 1), by have := u.isLt; omega⟩
        omega
      · rw [dif_neg hu2, dif_neg hv2] at huv
        have heq := hhi_inj huv
        have hval := congrArg Fin.val heq
        dsimp only at hval
        exact Fin.ext (by omega)

@[simp] private lemma triEmb_lo {A B W : ℕ}
    (lo : Fin A → Fin W) (mid : Fin W) (hi : Fin B → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin A, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin B, mid.1 < (hi j).1) (i : Fin A) :
    ((Fin.castAddEmb B).trans (triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi)) ⟨i.1, by omega⟩ =
      lo i := by
  change (if hw : i.1 < A then lo ⟨i.1, hw⟩ else _) = lo i
  rw [dif_pos i.isLt]

@[simp] private lemma triEmb_mid {A B W : ℕ}
    (lo : Fin A → Fin W) (mid : Fin W) (hi : Fin B → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin A, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin B, mid.1 < (hi j).1) :
    ((Fin.castAddEmb B).trans (triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi))
        ⟨A, Nat.lt_succ_self A⟩ = mid := by
  change (if hw : A < A then _ else if _ : A = A then mid else _) = mid
  rw [dif_neg (Nat.lt_irrefl A), dif_pos rfl]

@[simp] private lemma triEmb_hi {A B W : ℕ}
    (lo : Fin A → Fin W) (mid : Fin W) (hi : Fin B → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin A, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin B, mid.1 < (hi j).1) (j : Fin B) :
    triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi (Fin.natAdd (A + 1) j) = hi j := by
  have h1 : ¬ (Fin.natAdd (A + 1) j).1 < A := by simp; omega
  have h2 : ¬ (Fin.natAdd (A + 1) j).1 = A := by simp; omega
  change (if hw : (Fin.natAdd (A + 1) j).1 < A then _ else
    if _ : (Fin.natAdd (A + 1) j).1 = A then mid else
    hi ⟨(Fin.natAdd (A + 1) j).1 - (A + 1), _⟩) = hi j
  rw [dif_neg h1, dif_neg h2]
  congr 1; apply Fin.ext; simp

private lemma act_triEmb_multiEqCtrl1_ket {L W : ℕ}
    (lo : Fin L → Fin W) (mid : Fin W) (hi : Fin L → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin L, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin L, mid.1 < (hi j).1)
    (pat : Qubits L) (z : Qubits W)
    (hclean : ∀ j : Fin L, z (hi j) = false) :
    act ((multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).mapWires
        (triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi)).unitary (ket z) =
      ket (Function.update z mid (xor (z mid) (decide (∀ i : Fin L, z (lo i) = pat i)))) := by
  let emb := triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi
  let embMain : Fin (L + 1) ↪ Fin W := (Fin.castAddEmb L).trans emb
  have hclean' : ∀ j : Fin L, z (emb (Fin.natAdd (L + 1) j)) = false := fun j => by
    rw [show emb (Fin.natAdd (L + 1) j) = hi j from triEmb_hi _ _ _ _ _ _ _ j]
    exact hclean j
  rw [act_mapWires_perm _ _ (multiEqCtrl1_pauliX_implements L pat) emb z hclean']
  have htgt : ((Fin.castAddEmb L).trans emb) ⟨L, Nat.lt_succ_self L⟩ = mid := triEmb_mid _ _ _ _ _ _ _
  have hin : ∀ i : Fin L, z (((Fin.castAddEmb L).trans emb) ⟨i.1, by omega⟩) = z (lo i) := fun i => by
    rw [show ((Fin.castAddEmb L).trans emb) ⟨i.1, by omega⟩ = lo i from triEmb_lo _ _ _ _ _ _ _ i]
  congr 1; funext w
  by_cases hw : w = mid
  · subst hw
    rw [Function.update_self, ← htgt]
    change updateOn embMain z _ (embMain ⟨L, Nat.lt_succ_self L⟩) = _
    rw [updateOn_apply_emb, Function.update_self]
    dsimp only [Function.comp_apply]
    simp_rw [htgt, hin]
  · rw [Function.update_of_ne hw]
    by_cases hmem : w ∈ Set.range embMain
    · rcases hmem with ⟨i, rfl⟩
      rw [updateOn_apply_emb]
      have hne : i ≠ ⟨L, Nat.lt_succ_self L⟩ := fun h => hw (by rw [h]; exact htgt)
      exact Function.update_of_ne hne _ _
    · exact updateOn_apply_not_mem _ _ _ hmem

private lemma act_triEmb_ltConst_ket {q H W : ℕ}
    (lo : Fin q → Fin W) (mid : Fin W) (hi : Fin q → Fin W)
    (hlo_inj : Function.Injective lo) (hhi_inj : Function.Injective hi)
    (hlo_mid : ∀ i : Fin q, (lo i).1 < mid.1)
    (hmid_hi : ∀ j : Fin q, mid.1 < (hi j).1)
    (z : Qubits W)
    (hclean : ∀ j : Fin q, z (hi j) = false) :
    act ((ltConstCircuit q H).mapWires
        (triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi)).unitary (ket z) =
      ket (Function.update z mid
        (xor (z mid) (decide (bitsToNatLSB (fun i : Fin q => z (lo i)) < H)))) := by
  let emb := triEmb lo mid hi hlo_inj hhi_inj hlo_mid hmid_hi
  let embMain : Fin (q + 1) ↪ Fin W := (Fin.castAddEmb q).trans emb
  have hclean' : ∀ j : Fin q, z (emb (Fin.natAdd (q + 1) j)) = false := fun j => by
    rw [show emb (Fin.natAdd (q + 1) j) = hi j from triEmb_hi _ _ _ _ _ _ _ j]
    exact hclean j
  rw [act_mapWires_perm (ltConstCircuit q H) _ (ltConstCircuit_implements q H) emb z hclean']
  have htgt : ((Fin.castAddEmb q).trans emb) ⟨q, Nat.lt_succ_self q⟩ = mid := triEmb_mid _ _ _ _ _ _ _
  have hin : (fun i : Fin q => z (((Fin.castAddEmb q).trans emb) ⟨i.1, by omega⟩)) =
      fun i : Fin q => z (lo i) := by
    funext i; rw [show ((Fin.castAddEmb q).trans emb) ⟨i.1, by omega⟩ = lo i from triEmb_lo _ _ _ _ _ _ _ i]
  congr 1; funext w
  by_cases hw : w = mid
  · subst hw
    rw [Function.update_self, ← htgt]
    change updateOn embMain z _ (embMain ⟨q, Nat.lt_succ_self q⟩) = _
    rw [updateOn_apply_emb, Function.update_self]
    dsimp only [Function.comp_apply]
    rw [htgt]
    simp only [hin]
  · rw [Function.update_of_ne hw]
    by_cases hmem : w ∈ Set.range embMain
    · rcases hmem with ⟨i, rfl⟩
      rw [updateOn_apply_emb]
      have hne : i ≠ ⟨q, Nat.lt_succ_self q⟩ := fun h => hw (by rw [h]; exact htgt)
      exact Function.update_of_ne hne _ _
    · exact updateOn_apply_not_mem _ _ _ hmem

private lemma act_mapWires_multiEqCtrl1_pauliX_ket {L m : ℕ}
    (pat : Qubits L) (emb : Fin (L + 1 + L) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin L, z (emb (Fin.natAdd (L + 1) j)) = false) :
    act ((multiEqCtrl1 L pat pauliX pauliX_mem_unitaryGroup).mapWires emb).unitary (ket z) =
      ket (Function.update z (((Fin.castAddEmb L).trans emb) ⟨L, Nat.lt_succ_self L⟩)
        (xor (z (((Fin.castAddEmb L).trans emb) ⟨L, Nat.lt_succ_self L⟩))
          (decide (∀ i : Fin L, z (((Fin.castAddEmb L).trans emb) ⟨i.1, by omega⟩) = pat i)))) := by
  let embMain : Fin (L + 1) ↪ Fin m := (Fin.castAddEmb L).trans emb
  let tgtW : Fin m := embMain ⟨L, Nat.lt_succ_self L⟩
  rw [act_mapWires_perm _ _ (multiEqCtrl1_pauliX_implements L pat) emb z hclean]
  congr 1; funext w
  by_cases hw : w = tgtW
  · subst hw
    rw [Function.update_self]
    change updateOn embMain z _ (embMain ⟨L, Nat.lt_succ_self L⟩) = _
    rw [updateOn_apply_emb, Function.update_self]; rfl
  · rw [Function.update_of_ne hw]
    by_cases hmem : w ∈ Set.range embMain
    · rcases hmem with ⟨i, rfl⟩
      rw [updateOn_apply_emb]
      have hne : i ≠ ⟨L, Nat.lt_succ_self L⟩ := fun h => hw (congrArg embMain h)
      exact Function.update_of_ne hne _ _
    · exact updateOn_apply_not_mem _ _ _ hmem

private lemma bitsToNatLSB_trunc {q ℓ : ℕ} (v : Qubits q) :
    bitsToNatLSB (fun j : Fin ℓ => if h : j.1 < q then v ⟨j.1, h⟩ else false) =
      bitsToNatLSB v % 2 ^ ℓ := by
  by_cases hql : q ≤ ℓ
  · have hlt : bitsToNatLSB v < 2 ^ ℓ :=
      lt_of_lt_of_le (bitsToNatLSB_lt q v) (Nat.pow_le_pow_right (by norm_num) hql)
    rw [Nat.mod_eq_of_lt hlt]
    dsimp only [bitsToNatLSB]
    let img : Finset (Fin ℓ) := Finset.univ.image (Fin.castLEEmb hql)
    rw [← Finset.sum_sdiff (Finset.subset_univ img), add_comm]
    have hzero : (∑ j ∈ Finset.univ \ img,
        if (if h : j.1 < q then v ⟨j.1, h⟩ else false) = true then 2 ^ j.1 else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_not : j ∉ img := (Finset.mem_sdiff.mp hj).2
      have hnot_lt : ¬ j.1 < q := fun hltq => hj_not (Finset.mem_image.mpr
        ⟨⟨j.1, hltq⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp [hnot_lt]
    have himg : (∑ j ∈ img,
        if (if h : j.1 < q then v ⟨j.1, h⟩ else false) = true then 2 ^ j.1 else 0) =
        ∑ i : Fin q, if v i = true then 2 ^ i.1 else 0 := by
      rw [Finset.sum_image (by
        intro a _ b _ hab
        exact Fin.ext (by simpa using congrArg Fin.val hab))]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi := i.isLt
      simp [Fin.castLEEmb, hi]
    rw [himg, hzero, add_zero]
  · have hlq : ℓ < q := Nat.lt_of_not_ge hql
    dsimp only [bitsToNatLSB]
    let emb : Fin ℓ ↪ Fin q := Fin.castLEEmb (le_of_lt hlq)
    let low : Finset (Fin q) := Finset.univ.image emb
    have hsplit : (∑ i : Fin q, if v i = true then 2 ^ i.1 else 0) =
        (∑ i ∈ low, if v i = true then 2 ^ i.1 else 0) +
        (∑ i ∈ Finset.univ \ low, if v i = true then 2 ^ i.1 else 0) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ low), add_comm]
    have hlow : (∑ i ∈ low, if v i = true then 2 ^ i.1 else 0) =
        ∑ j : Fin ℓ,
          if (if h : j.1 < q then v ⟨j.1, h⟩ else false) = true then 2 ^ j.1 else 0 := by
      rw [Finset.sum_image (by
        intro a _ b _ hab
        dsimp only [emb] at hab
        exact Fin.ext (by simpa using congrArg Fin.val hab))]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : j.1 < q := lt_trans j.isLt hlq
      have hcast : emb j = ⟨j.1, hj⟩ := Fin.ext rfl
      rw [hcast]
      simp [hj]
    have hdvd : 2 ^ ℓ ∣ ∑ i ∈ Finset.univ \ low, if v i = true then 2 ^ i.1 else 0 := by
      refine Finset.dvd_sum fun i hi => ?_
      have hi_not : i ∉ low := (Finset.mem_sdiff.mp hi).2
      have hge : ℓ ≤ i.1 := by
        by_contra hlt
        apply hi_not
        exact Finset.mem_image.mpr ⟨⟨i.1, Nat.lt_of_not_ge hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      by_cases hvi : v i = true
      · rw [if_pos hvi]; exact Nat.pow_dvd_pow 2 hge
      · rw [if_neg hvi]; exact dvd_zero _
    rcases hdvd with ⟨Q, hQ⟩
    have hlt_pow : (∑ j : Fin ℓ,
        if (if h : j.1 < q then v ⟨j.1, h⟩ else false) = true then 2 ^ j.1 else 0) < 2 ^ ℓ :=
      bitsToNatLSB_lt ℓ (fun j => if h : j.1 < q then v ⟨j.1, h⟩ else false)
    rw [hsplit, hlow, hQ, add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_pow]

private lemma degree_sum_lt_pow_ell (n D : ℕ) (α : Fin n → ℕ) (hD : ∀ i, α i < D) :
    ∑ i : Fin n, α i < 2 ^ (Nat.clog 2 (n * D + 2) + 1) := by
  calc
    ∑ i : Fin n, α i ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ => le_of_lt (hD i)
    _ = n * D := by simp
    _ < n * D + 2 := by omega
    _ ≤ 2 ^ Nat.clog 2 (n * D + 2) := Nat.le_pow_clog (by norm_num) (n * D + 2)
    _ ≤ 2 ^ (Nat.clog 2 (n * D + 2) + 1) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _)

/-! #### 3a. Generic Out-of-Place Ripple-Carry `ℓ`-bit Adder -/

private noncomputable def rippleAddBits {W ℓ : ℕ}
    (aW bW sW : Fin ℓ → Fin W) (cW : Fin (ℓ + 1) → Fin W)
    (hab : ∀ j : Fin ℓ, aW j ≠ bW j)
    (has : ∀ j k : Fin ℓ, aW j ≠ sW k)
    (haco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), aW j ≠ cW k)
    (hbs : ∀ j k : Fin ℓ, bW j ≠ sW k)
    (hbco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), bW j ≠ cW k)
    (hcs : ∀ (k : Fin (ℓ + 1)) (j : Fin ℓ), cW k ≠ sW j)
    (hsinj : Function.Injective sW)
    (hcinj : Function.Injective cW) :
    (k : ℕ) → k ≤ ℓ → LayeredCircuit W
  | 0, _ => LayeredCircuit.id W
  | k + 1, hk =>
    let prev := rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj k (by omega)
    let jk : Fin ℓ := ⟨k, hk⟩
    let ck : Fin (ℓ + 1) := ⟨k, by omega⟩
    let ck1 : Fin (ℓ + 1) := ⟨k + 1, by omega⟩
    let step := fullAdder5 (aW jk) (bW jk) (cW ck) (sW jk) (cW ck1)
      (hab jk) (has jk jk) (haco jk ck1) (hbs jk jk) (hbco jk ck1)
      (hcs ck jk) (hcinj.ne (by simp [ck, ck1])) ((hcs ck1 jk).symm)
    prev.seq step

private lemma rippleAddBits_size {W ℓ : ℕ}
    (aW bW sW : Fin ℓ → Fin W) (cW : Fin (ℓ + 1) → Fin W)
    (hab : ∀ j : Fin ℓ, aW j ≠ bW j)
    (has : ∀ j k : Fin ℓ, aW j ≠ sW k)
    (haco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), aW j ≠ cW k)
    (hbs : ∀ j k : Fin ℓ, bW j ≠ sW k)
    (hbco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), bW j ≠ cW k)
    (hcs : ∀ (k : Fin (ℓ + 1)) (j : Fin ℓ), cW k ≠ sW j)
    (hsinj : Function.Injective sW)
    (hcinj : Function.Injective cW)
    (k : ℕ) (hk : k ≤ ℓ) :
    (rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj k hk).size = 13 * k := by
  induction k with
  | zero => simp [rippleAddBits]
  | succ k ih =>
    simp [rippleAddBits, ih (by omega)]; omega

private lemma prefSum_succ {ℓ : ℕ} (v : Fin ℓ → Bool) (k : ℕ) (hk : k + 1 ≤ ℓ) :
    (∑ t : Fin ℓ, if t.1 < k + 1 then (if v t = true then 2 ^ t.1 else 0) else 0) =
      (∑ t : Fin ℓ, if t.1 < k then (if v t = true then 2 ^ t.1 else 0) else 0) +
        (if v ⟨k, hk⟩ = true then 2 ^ k else 0) := by
  let jk : Fin ℓ := ⟨k, hk⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ jk),
    ← Finset.add_sum_erase Finset.univ (fun t : Fin ℓ =>
      if t.1 < k then (if v t = true then 2 ^ t.1 else 0) else 0) (Finset.mem_univ jk)]
  have h1 : (if jk.1 < k + 1 then (if v jk = true then 2 ^ jk.1 else 0) else 0) =
      (if v jk = true then 2 ^ k else 0) := by simp [jk]
  have h2 : (if jk.1 < k then (if v jk = true then 2 ^ jk.1 else 0) else 0) = 0 := by
    simp [jk]
  have hrest : (∑ t ∈ Finset.univ.erase jk,
      if t.1 < k + 1 then (if v t = true then 2 ^ t.1 else 0) else 0) =
      ∑ t ∈ Finset.univ.erase jk,
        if t.1 < k then (if v t = true then 2 ^ t.1 else 0) else 0 := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hne : t.1 ≠ k := fun h => (Finset.mem_erase.mp ht).1 (Fin.ext h)
    have hiff : t.1 < k + 1 ↔ t.1 < k := by omega
    simp only [hiff]
  rw [h1, h2, zero_add, hrest, add_comm]

private lemma rippleAddBits_act {W ℓ : ℕ}
    (aW bW sW : Fin ℓ → Fin W) (cW : Fin (ℓ + 1) → Fin W)
    (hab : ∀ j : Fin ℓ, aW j ≠ bW j)
    (has : ∀ j k : Fin ℓ, aW j ≠ sW k)
    (haco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), aW j ≠ cW k)
    (hbs : ∀ j k : Fin ℓ, bW j ≠ sW k)
    (hbco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), bW j ≠ cW k)
    (hcs : ∀ (k : Fin (ℓ + 1)) (j : Fin ℓ), cW k ≠ sW j)
    (hsinj : Function.Injective sW)
    (hcinj : Function.Injective cW)
    (k : ℕ) (hk : k ≤ ℓ) (z : Qubits W)
    (hzs : ∀ t : Fin ℓ, z (sW t) = false)
    (hzc : ∀ t : Fin (ℓ + 1), z (cW t) = false) :
    ∃ z' : Qubits W,
      act (rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj k hk).unitary (ket z) =
        ket z' ∧
      (∀ w : Fin W, (∀ t : Fin ℓ, w ≠ sW t) → (∀ t : Fin (ℓ + 1), w ≠ cW t) → z' w = z w) ∧
      (∀ t : Fin ℓ, k ≤ t.1 → z' (sW t) = false) ∧
      (∀ t : Fin (ℓ + 1), k < t.1 → z' (cW t) = false) ∧
      z' (cW 0) = false ∧
      (∑ t : Fin ℓ, if t.1 < k then (if z' (sW t) = true then 2 ^ t.1 else 0) else 0) +
          2 ^ k * (if z' (cW ⟨k, by omega⟩) = true then 1 else 0) =
        (∑ t : Fin ℓ, if t.1 < k then (if z (aW t) = true then 2 ^ t.1 else 0) else 0) +
        (∑ t : Fin ℓ, if t.1 < k then (if z (bW t) = true then 2 ^ t.1 else 0) else 0) := by
  induction k with
  | zero =>
    refine ⟨z, ?_, fun w _ _ => rfl, fun t _ => hzs t, fun t _ => hzc t, hzc 0, ?_⟩
    · simp [rippleAddBits, act_one]
    · simp [hzc 0]
  | succ k ih =>
    rcases ih (by omega) with ⟨z1, h1_act, h1_pres, h1_s, h1_c, h1_c0, h1_sum⟩
    let jk : Fin ℓ := ⟨k, hk⟩
    let ck : Fin (ℓ + 1) := ⟨k, by omega⟩
    let ck1 : Fin (ℓ + 1) := ⟨k + 1, by omega⟩
    let a := aW jk
    let b := bW jk
    let c := cW ck
    let s := sW jk
    let cout := cW ck1
    have hzs_clean : z1 s = false := h1_s jk (by simp [jk])
    have hzc_clean : z1 cout = false := h1_c ck1 (by simp [ck1])
    have hstep := act_fullAdder5_ket a b c s cout
      (hab jk) (has jk jk) (haco jk ck1) (hbs jk jk) (hbco jk ck1)
      (hcs ck jk) (hcinj.ne (by simp [ck, ck1])) ((hcs ck1 jk).symm) z1 hzs_clean hzc_clean
    let z2 : Qubits W := fun w =>
      if w = s then xor (xor (z1 a) (z1 b)) (z1 c)
      else if w = cout then xor (z1 a && z1 b) (xor (z1 a) (z1 b) && z1 c)
      else z1 w
    have htot : act (rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj
        (k + 1) hk).unitary (ket z) = ket z2 := by
      dsimp only [rippleAddBits]
      rw [LayeredCircuit.seq_unitary, act_mul, h1_act]
      exact hstep
    have hza : z1 a = z a := h1_pres a (fun t => has _ t) (fun t => haco _ t)
    have hzb : z1 b = z b := h1_pres b (fun t => hbs _ t) (fun t => hbco _ t)
    refine ⟨z2, htot, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hws hwc
      dsimp only [z2]
      rw [if_neg (hws jk), if_neg (hwc ck1), h1_pres w hws hwc]
    · intro t ht
      have hne_s : sW t ≠ s := hsinj.ne (by intro h; have := congrArg Fin.val h; simp [jk] at this; omega)
      have hne_c : sW t ≠ cout := (hcs ck1 t).symm
      dsimp only [z2]; rw [if_neg hne_s, if_neg hne_c]; exact h1_s t (by omega)
    · intro t ht
      have hne_s : cW t ≠ s := hcs t jk
      have hne_c : cW t ≠ cout := hcinj.ne (by intro h; have := congrArg Fin.val h; simp [ck1] at this; omega)
      dsimp only [z2]; rw [if_neg hne_s, if_neg hne_c]; exact h1_c t (by omega)
    · have hne_s : cW 0 ≠ s := hcs 0 jk
      have hne_c : cW 0 ≠ cout := hcinj.ne (by intro h; have := congrArg Fin.val h; simp [ck1] at this)
      dsimp only [z2]; rw [if_neg hne_s, if_neg hne_c]; exact h1_c0
    · rw [prefSum_succ (fun t => z2 (sW t)) k hk,
        prefSum_succ (fun t => z (aW t)) k hk,
        prefSum_succ (fun t => z (bW t)) k hk]
      have hpref_eq :
          (∑ t : Fin ℓ, if t.1 < k then (if z2 (sW t) = true then 2 ^ t.1 else 0) else 0) =
            ∑ t : Fin ℓ, if t.1 < k then (if z1 (sW t) = true then 2 ^ t.1 else 0) else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases ht : t.1 < k
        · rw [if_pos ht, if_pos ht]
          have hne_s : sW t ≠ s := hsinj.ne (by intro h; have := congrArg Fin.val h; simp [jk] at this; omega)
          have hne_c : sW t ≠ cout := (hcs ck1 t).symm
          have hz2_eq : z2 (sW t) = z1 (sW t) := by
            dsimp only [z2]; rw [if_neg hne_s, if_neg hne_c]
          simp only [hz2_eq]
        · rw [if_neg ht, if_neg ht]
      have hs_val : z2 (sW jk) = xor (xor (z a) (z b)) (z1 c) := by
        dsimp only [z2]; rw [if_pos rfl, hza, hzb]
      have hc_val : z2 (cW ck1) = xor (z a && z b) (xor (z a) (z b) && z1 c) := by
        have hcs' : cout ≠ s := hcs ck1 jk
        dsimp only [z2]; rw [if_neg hcs', if_pos rfl, hza, hzb]
      have harith := bool_fullAdder_arith (z a) (z b) (z1 c)
      have harith2 :
          (if z2 (sW jk) = true then 2 ^ k else 0) +
            2 ^ (k + 1) * (if z2 (cW ck1) = true then 1 else 0) =
          (if z a = true then 2 ^ k else 0) +
            (if z b = true then 2 ^ k else 0) +
            2 ^ k * (if z1 c = true then 1 else 0) := by
        rw [hs_val, hc_val, pow_succ']
        have hmul := congrArg (fun u => 2 ^ k * u) harith
        have hite : ∀ (p : Bool), (if p = true then 2 ^ k else 0) = 2 ^ k * (if p = true then 1 else 0) := by
          intro p; cases p <;> simp
        simp only [hite] at hmul ⊢
        linarith
      rw [hpref_eq]
      change _ + _ + 2 ^ (k + 1) * (if z2 (cW ck1) = true then 1 else 0) = _
      linarith

private lemma rippleAddBits_full {W ℓ : ℕ}
    (aW bW sW : Fin ℓ → Fin W) (cW : Fin (ℓ + 1) → Fin W)
    (hab : ∀ j : Fin ℓ, aW j ≠ bW j)
    (has : ∀ j k : Fin ℓ, aW j ≠ sW k)
    (haco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), aW j ≠ cW k)
    (hbs : ∀ j k : Fin ℓ, bW j ≠ sW k)
    (hbco : ∀ (j : Fin ℓ) (k : Fin (ℓ + 1)), bW j ≠ cW k)
    (hcs : ∀ (k : Fin (ℓ + 1)) (j : Fin ℓ), cW k ≠ sW j)
    (hsinj : Function.Injective sW)
    (hcinj : Function.Injective cW)
    (z : Qubits W)
    (hzs : ∀ t : Fin ℓ, z (sW t) = false)
    (hzc : ∀ t : Fin (ℓ + 1), z (cW t) = false) :
    ∃ z' : Qubits W,
      act (rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj ℓ le_rfl).unitary (ket z) =
        ket z' ∧
      (∀ w : Fin W, (∀ t : Fin ℓ, w ≠ sW t) → (∀ t : Fin (ℓ + 1), w ≠ cW t) → z' w = z w) ∧
      bitsToNatLSB (fun t : Fin ℓ => z' (sW t)) =
        (bitsToNatLSB (fun t : Fin ℓ => z (aW t)) + bitsToNatLSB (fun t : Fin ℓ => z (bW t))) % 2 ^ ℓ := by
  rcases rippleAddBits_act aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj ℓ le_rfl z hzs hzc
    with ⟨z', hact, hpres, _, _, _, hsum⟩
  have heq_sum : ∀ f : Fin ℓ → Bool,
      (∑ t : Fin ℓ, if t.1 < ℓ then (if f t = true then 2 ^ t.1 else 0) else 0) = bitsToNatLSB f := by
    intro f; dsimp only [bitsToNatLSB]
    refine Finset.sum_congr rfl fun t _ => by simp [t.isLt]
  rw [heq_sum, heq_sum, heq_sum] at hsum
  have hmod := congrArg (· % 2 ^ ℓ) hsum
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bitsToNatLSB_lt ℓ _)] at hmod
  exact ⟨z', hact, hpres, hmod⟩

/-! #### 3b. Wire Layout & `goodFlagCompute` -/

private abbrev gfEll (n D : ℕ) : ℕ := Nat.clog 2 (n * D + 2) + 1

private abbrev gfAnc (n D q a : ℕ) : ℕ :=
  1 + a + n + q + 1 + n + 1 + (n + 1) * gfEll n D + n * (gfEll n D + 1) +
    1 + 1 + gfEll n D + 5

private abbrev gfW (n D q a : ℕ) : ℕ := (n * q + 1 + a) + (1 + gfAnc n D q a)

private abbrev gfOffAcc (n q a : ℕ) : ℕ := n * q + 1 + a + 4 + a + 2 * n + q

private abbrev gfOffCarry (n D q a : ℕ) : ℕ := gfOffAcc n q a + (n + 1) * gfEll n D

private abbrev gfOffTail (n D q a : ℕ) : ℕ := gfOffCarry n D q a + n * (gfEll n D + 1)

private def gfWireX (n D q a : ℕ) (i : Fin n) (j : Fin q) : Fin (gfW n D q a) :=
  ⟨(finProdFinEquiv (i, j)).1, by
    have hlt := (finProdFinEquiv (i, j)).isLt
    dsimp [gfW, gfAnc]; omega⟩

private def gfWireY (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨n * q, by dsimp [gfW, gfAnc]; omega⟩

private def gfWireS (n D q a : ℕ) (j : Fin a) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + j.1, by have := j.isLt; dsimp [gfW, gfAnc]; omega⟩

private def gfWireOut (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a, by dsimp [gfW, gfAnc]; omega⟩

private def gfWireFS (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 1, by dsimp [gfW, gfAnc]; omega⟩

private def gfWireAncS (n D q a : ℕ) (j : Fin a) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 2 + j.1, by have := j.isLt; dsimp [gfW, gfAnc]; omega⟩

private def gfWireFD (n D q a : ℕ) (i : Fin n) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 2 + a + i.1, by have := i.isLt; dsimp [gfW, gfAnc]; omega⟩

private def gfWireAncCmpQ (n D q a : ℕ) (j : Fin q) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 2 + a + n + j.1, by have := j.isLt; dsimp [gfW, gfAnc]; omega⟩

private def gfWireFDAll (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 2 + a + n + q, by dsimp [gfW, gfAnc]; omega⟩

private def gfWireAncAndD (n D q a : ℕ) (i : Fin n) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 3 + a + n + q + i.1, by have := i.isLt; dsimp [gfW, gfAnc]; omega⟩

private def gfWireZero (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨n * q + 1 + a + 3 + a + 2 * n + q, by dsimp [gfW, gfAnc]; omega⟩

private def gfWireAcc (n D q a : ℕ) (i : Fin (n + 1)) (j : Fin (gfEll n D)) : Fin (gfW n D q a) :=
  ⟨gfOffAcc n q a + i.1 * gfEll n D + j.1, by
    have hlt := fin_prod_lt i j
    dsimp [gfW, gfAnc, gfOffAcc]; omega⟩

private def gfWireCarry (n D q a : ℕ) (i : Fin n) (k : Fin (gfEll n D + 1)) : Fin (gfW n D q a) :=
  ⟨gfOffCarry n D q a + i.1 * (gfEll n D + 1) + k.1, by
    have hlt := fin_prod_lt i k
    dsimp [gfW, gfAnc, gfOffCarry, gfOffAcc]; omega⟩

private def gfWireFLtK (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨gfOffTail n D q a, by dsimp [gfW, gfAnc, gfOffTail, gfOffCarry, gfOffAcc]; omega⟩

private def gfWireFLt2K1 (n D q a : ℕ) : Fin (gfW n D q a) :=
  ⟨gfOffTail n D q a + 1, by dsimp [gfW, gfAnc, gfOffTail, gfOffCarry, gfOffAcc]; omega⟩

private def gfWireAncCmpL (n D q a : ℕ) (j : Fin (gfEll n D)) : Fin (gfW n D q a) :=
  ⟨gfOffTail n D q a + 2 + j.1, by have := j.isLt; dsimp [gfW, gfAnc, gfOffTail, gfOffCarry, gfOffAcc]; omega⟩

private def gfWireAncComb (n D q a : ℕ) (k : Fin 5) : Fin (gfW n D q a) :=
  ⟨gfOffTail n D q a + 2 + gfEll n D + k.1, by have := k.isLt; dsimp [gfW, gfAnc, gfOffTail, gfOffCarry, gfOffAcc]; omega⟩

private lemma gfWireAcc_lt_carry (n D q a : ℕ) (i : Fin (n + 1)) (j : Fin (gfEll n D)) :
    (gfWireAcc n D q a i j).1 < gfOffCarry n D q a := by
  have h := fin_prod_lt i j
  dsimp [gfWireAcc, gfOffCarry]; omega

private lemma gfWireAcc_lt_tail (n D q a : ℕ) (i : Fin (n + 1)) (j : Fin (gfEll n D)) :
    (gfWireAcc n D q a i j).1 < gfOffTail n D q a := by
  have h := gfWireAcc_lt_carry n D q a i j
  dsimp [gfOffTail]; omega

private lemma gfWireCarry_lt_tail (n D q a : ℕ) (i : Fin n) (k : Fin (gfEll n D + 1)) :
    (gfWireCarry n D q a i k).1 < gfOffTail n D q a := by
  have h := fin_prod_lt i k
  dsimp [gfWireCarry, gfOffTail]; omega

private def gfEqSEmb (n D q a : ℕ) : Fin (a + 1 + a) ↪ Fin (gfW n D q a) :=
  triEmb (gfWireS n D q a) (gfWireFS n D q a) (gfWireAncS n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireS] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncS] at hv; omega))
    (fun i => by have := i.isLt; dsimp [gfWireS, gfWireFS]; omega)
    (fun j => by dsimp [gfWireFS, gfWireAncS]; omega)

private def gfCmpDEmb (n D q a : ℕ) (i : Fin n) : Fin (q + 1 + q) ↪ Fin (gfW n D q a) :=
  triEmb (fun j => gfWireX n D q a i j.rev) (gfWireFD n D q a i) (gfWireAncCmpQ n D q a)
    (fun u v h => by
      have hv := congrArg Fin.val h; dsimp [gfWireX] at hv
      have hpair := congrArg Prod.snd (finProdFinEquiv.injective (Fin.ext hv))
      exact Fin.rev_inj.mp hpair)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpQ] at hv; omega))
    (fun j => by
      have hlt := (finProdFinEquiv (i, j.rev)).isLt
      dsimp [gfWireX, gfWireFD]; omega)
    (fun j => by have := i.isLt; dsimp [gfWireFD, gfWireAncCmpQ]; omega)

private def gfAndDEmb (n D q a : ℕ) : Fin (n + 1 + n) ↪ Fin (gfW n D q a) :=
  triEmb (gfWireFD n D q a) (gfWireFDAll n D q a) (gfWireAncAndD n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireFD] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncAndD] at hv; omega))
    (fun i => by have := i.isLt; dsimp [gfWireFD, gfWireFDAll]; omega)
    (fun j => by dsimp [gfWireFDAll, gfWireAncAndD]; omega)

private def gfCmpKEmb (n D q a : ℕ) : Fin (gfEll n D + 1 + gfEll n D) ↪ Fin (gfW n D q a) :=
  triEmb (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩) (gfWireFLtK n D q a) (gfWireAncCmpL n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAcc] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpL] at hv; omega))
    (fun j => by have h := gfWireAcc_lt_tail n D q a ⟨n, Nat.lt_succ_self n⟩ j; dsimp [gfWireFLtK]; omega)
    (fun j => by dsimp [gfWireFLtK, gfWireAncCmpL]; omega)

private def gfCmp2K1Emb (n D q a : ℕ) : Fin (gfEll n D + 1 + gfEll n D) ↪ Fin (gfW n D q a) :=
  triEmb (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩) (gfWireFLt2K1 n D q a) (gfWireAncCmpL n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAcc] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpL] at hv; omega))
    (fun j => by have h := gfWireAcc_lt_tail n D q a ⟨n, Nat.lt_succ_self n⟩ j; dsimp [gfWireFLt2K1]; omega)
    (fun j => by dsimp [gfWireFLt2K1, gfWireAncCmpL]; omega)

private def gfCombWire (n D q a : ℕ) (w : Fin (5 + 1 + 5)) : Fin (gfW n D q a) :=
  if w.1 = 0 then gfWireY n D q a
  else if w.1 = 1 then gfWireFS n D q a
  else if w.1 = 2 then gfWireFDAll n D q a
  else if w.1 = 3 then gfWireFLtK n D q a
  else if w.1 = 4 then gfWireFLt2K1 n D q a
  else if w.1 = 5 then gfWireOut n D q a
  else gfWireAncComb n D q a ⟨w.1 - 6, by have := w.isLt; omega⟩

private def gfCombInv (n D q a : ℕ) (x : ℕ) : ℕ :=
  if x = n * q then 0
  else if x = n * q + 1 + a then 5
  else if x = n * q + 1 + a + 1 then 1
  else if x = n * q + 1 + a + 2 + a + n + q then 2
  else if x = gfOffTail n D q a then 3
  else if x = gfOffTail n D q a + 1 then 4
  else x - (gfOffTail n D q a + 2 + gfEll n D) + 6

private lemma gfCombInv_left (n D q a : ℕ) (w : Fin (5 + 1 + 5)) :
    gfCombInv n D q a (gfCombWire n D q a w).1 = w.1 := by
  have htail : n * q + 1 + a + 2 + a + n + q < gfOffTail n D q a := by
    dsimp [gfOffTail, gfOffCarry, gfOffAcc]; omega
  dsimp only [gfCombWire, gfCombInv]
  rcases eq_or_ne w.1 0 with h0 | h0
  · rw [if_pos h0, if_pos (by dsimp [gfWireY]), h0]
  · rw [if_neg h0]
    rcases eq_or_ne w.1 1 with h1 | h1
    · rw [if_pos h1, if_neg (by dsimp [gfWireFS]; omega), if_neg (by dsimp [gfWireFS]; omega),
        if_pos (by dsimp [gfWireFS]), h1]
    · rw [if_neg h1]
      rcases eq_or_ne w.1 2 with h2 | h2
      · rw [if_pos h2, if_neg (by dsimp [gfWireFDAll]; omega), if_neg (by dsimp [gfWireFDAll]; omega),
          if_neg (by dsimp [gfWireFDAll]; omega), if_pos (by dsimp [gfWireFDAll]), h2]
      · rw [if_neg h2]
        rcases eq_or_ne w.1 3 with h3 | h3
        · rw [if_pos h3, if_neg (by dsimp [gfWireFLtK]; omega), if_neg (by dsimp [gfWireFLtK]; omega),
            if_neg (by dsimp [gfWireFLtK]; omega), if_neg (by dsimp [gfWireFLtK]; omega),
            if_pos (by dsimp [gfWireFLtK]), h3]
        · rw [if_neg h3]
          rcases eq_or_ne w.1 4 with h4 | h4
          · rw [if_pos h4, if_neg (by dsimp [gfWireFLt2K1]; omega), if_neg (by dsimp [gfWireFLt2K1]; omega),
              if_neg (by dsimp [gfWireFLt2K1]; omega), if_neg (by dsimp [gfWireFLt2K1]; omega),
              if_neg (by dsimp [gfWireFLt2K1]; omega), if_pos (by dsimp [gfWireFLt2K1]), h4]
          · rw [if_neg h4]
            rcases eq_or_ne w.1 5 with h5 | h5
            · rw [if_pos h5, if_neg (by dsimp [gfWireOut]; omega), if_pos (by dsimp [gfWireOut]), h5]
            · rw [if_neg h5, if_neg (by dsimp [gfWireAncComb]; omega),
                if_neg (by dsimp [gfWireAncComb]; omega), if_neg (by dsimp [gfWireAncComb]; omega),
                if_neg (by dsimp [gfWireAncComb]; omega), if_neg (by dsimp [gfWireAncComb]; omega),
                if_neg (by dsimp [gfWireAncComb]; omega)]
              dsimp [gfWireAncComb]; omega

private def gfCombEmb (n D q a : ℕ) : Fin (5 + 1 + 5) ↪ Fin (gfW n D q a) where
  toFun := gfCombWire n D q a
  inj' u v huv := by
    have h1 := gfCombInv_left n D q a u
    have h2 := gfCombInv_left n D q a v
    rw [congrArg Fin.val huv] at h1
    exact Fin.ext (h1.symm.trans h2)

private noncomputable def gfCmpDLoop (n D q a : ℕ) : (k : ℕ) → k ≤ n → LayeredCircuit (gfW n D q a)
  | 0, _ => LayeredCircuit.id (gfW n D q a)
  | k + 1, hk =>
    (gfCmpDLoop n D q a k (by omega)).seq
      ((ltConstCircuit q D).mapWires (gfCmpDEmb n D q a ⟨k, hk⟩))

private lemma gfCmpDLoop_size (n D q a k : ℕ) (hk : k ≤ n) :
    (gfCmpDLoop n D q a k hk).size ≤ k * (16 * q + 1) := by
  induction k with
  | zero => simp [gfCmpDLoop]
  | succ k ih =>
    simp only [gfCmpDLoop, LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
    have h1 := ih (by omega)
    have h2 := ltConstCircuit_size q D
    nlinarith

private def gfCmpDState (n D q a k : ℕ) (hk : k ≤ n) (z : Qubits (gfW n D q a)) :
    Qubits (gfW n D q a) :=
  fun w =>
    if _ : n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + k then
      let xBits : Qubits (n * q) := fun t => z ⟨t.1, by have := t.isLt; dsimp [gfW, gfAnc]; omega⟩
      decide (bitsToNat (splitReg n q xBits ⟨w.1 - (n * q + 1 + a + 2 + a), by omega⟩) < D)
    else z w

private lemma gfCmpDLoop_act (n D q a k : ℕ) (hk : k ≤ n) (z : Qubits (gfW n D q a))
    (hfd : ∀ i : Fin n, z (gfWireFD n D q a i) = false)
    (hanc : ∀ j : Fin q, z (gfWireAncCmpQ n D q a j) = false) :
    act (gfCmpDLoop n D q a k hk).unitary (ket z) = ket (gfCmpDState n D q a k hk z) := by
  induction k with
  | zero =>
    simp only [gfCmpDLoop, LayeredCircuit.id_unitary, act_one]
    congr 1; funext w; dsimp only [gfCmpDState]; rw [dif_neg (by omega)]
  | succ k ih =>
    have hih : act (gfCmpDLoop n D q a k (by omega)).unitary (ket z) =
        ket (gfCmpDState n D q a k (by omega) z) := ih (by omega)
    let ik : Fin n := ⟨k, hk⟩
    have hclean : ∀ j : Fin q,
        gfCmpDState n D q a k (by omega) z (gfWireAncCmpQ n D q a j) = false := fun j => by
      dsimp only [gfCmpDState]
      rw [dif_neg (by dsimp [gfWireAncCmpQ]; omega)]
      exact hanc j
    have hstep := act_triEmb_ltConst_ket (H := D)
      (fun j => gfWireX n D q a ik j.rev) (gfWireFD n D q a ik) (gfWireAncCmpQ n D q a)
      (fun u v h => by
        have hv := congrArg Fin.val h; dsimp [gfWireX] at hv
        exact Fin.rev_inj.mp (congrArg Prod.snd (finProdFinEquiv.injective (Fin.ext hv))))
      (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpQ] at hv; omega))
      (fun j => by have hlt := (finProdFinEquiv (ik, j.rev)).isLt; dsimp [gfWireX, gfWireFD]; omega)
      (fun j => by have := ik.isLt; dsimp [gfWireFD, gfWireAncCmpQ]; omega)
      (gfCmpDState n D q a k (by omega) z) hclean
    dsimp only [gfCmpDLoop, gfCmpDEmb] at hstep ⊢
    rw [LayeredCircuit.seq_unitary, act_mul, hih, hstep]
    congr 1; funext w
    by_cases hw : w = gfWireFD n D q a ik
    · subst hw
      rw [Function.update_self]
      have htgt_val : gfCmpDState n D q a k (by omega) z (gfWireFD n D q a ik) = false := by
        dsimp only [gfCmpDState]; rw [dif_neg (by dsimp [gfWireFD, ik]; omega)]; exact hfd ik
      have hin_eq : (fun j : Fin q =>
          gfCmpDState n D q a k (by omega) z (gfWireX n D q a ik j.rev)) =
          fun j : Fin q => splitReg n q
            (fun t => z ⟨t.1, by have := t.isLt; dsimp [gfW, gfAnc]; omega⟩) ik j.rev := by
        funext j; dsimp only [gfCmpDState]
        rw [dif_neg (by have := (finProdFinEquiv (ik, j.rev)).isLt; dsimp [gfWireX]; omega)]; rfl
      simp only [htgt_val, Bool.false_xor, hin_eq, bitsToNatLSB_rev]
      dsimp only [gfCmpDState]
      have hcond : n * q + 1 + a + 2 + a ≤ (gfWireFD n D q a ik).1 ∧
          (gfWireFD n D q a ik).1 < n * q + 1 + a + 2 + a + (k + 1) := by
        dsimp [gfWireFD, ik]; omega
      rw [dif_pos hcond]
      have hidx : (⟨(gfWireFD n D q a ik).1 - (n * q + 1 + a + 2 + a), by
          dsimp [gfWireFD, ik]; omega⟩ : Fin n) = ik := by
        apply Fin.ext; simp [gfWireFD, ik]
      simp only [hidx]
    · rw [Function.update_of_ne hw]
      dsimp only [gfCmpDState]
      by_cases hwin : n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + k
      · have hwin' : n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + (k + 1) := by omega
        rw [dif_pos hwin, dif_pos hwin']
      · have hwout' : ¬ (n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + (k + 1)) := by
          intro h; apply hw; apply Fin.ext; dsimp [gfWireFD, ik]; omega
        rw [dif_neg hwin, dif_neg hwout']

private def gfWireB (n D q a : ℕ) (i : Fin n) (j : Fin (gfEll n D)) : Fin (gfW n D q a) :=
  if hj : j.1 < q then gfWireX n D q a i (⟨j.1, hj⟩ : Fin q).rev else gfWireZero n D q a

private noncomputable def gfAccStep (n D q a : ℕ) (i : Fin n) : LayeredCircuit (gfW n D q a) :=
  let aW := gfWireAcc n D q a i.castSucc
  let bW := gfWireB n D q a i
  let sW := gfWireAcc n D q a i.succ
  let cW := gfWireCarry n D q a i
  have hab : ∀ j : Fin (gfEll n D), aW j ≠ bW j := fun j => by
    intro h; have hv := congrArg Fin.val h
    dsimp [aW, bW, gfWireB, gfWireAcc, gfOffAcc] at hv
    split_ifs at hv with hj
    · have hlt := (finProdFinEquiv (i, (⟨j.1, hj⟩ : Fin q).rev)).isLt
      dsimp [gfWireX] at hv; omega
    · dsimp [gfWireZero] at hv; omega
  have has : ∀ j k : Fin (gfEll n D), aW j ≠ sW k := fun j k => by
    intro h; have hv := congrArg Fin.val h
    dsimp [aW, sW, gfWireAcc] at hv
    have hj := j.isLt
    have hmul : i.1 * gfEll n D + gfEll n D = (i.1 + 1) * gfEll n D := by ring
    omega
  have haco : ∀ (j : Fin (gfEll n D)) (k : Fin (gfEll n D + 1)), aW j ≠ cW k := fun j k => by
    intro h; have hv := congrArg Fin.val h
    have ha := gfWireAcc_lt_carry n D q a i.castSucc j
    dsimp [aW, cW, gfWireCarry] at ha hv; omega
  have hbs : ∀ j k : Fin (gfEll n D), bW j ≠ sW k := fun j k => by
    intro h; have hv := congrArg Fin.val h
    dsimp [bW, sW, gfWireB, gfWireAcc, gfOffAcc] at hv
    split_ifs at hv with hj
    · have hlt := (finProdFinEquiv (i, (⟨j.1, hj⟩ : Fin q).rev)).isLt
      dsimp [gfWireX] at hv; omega
    · dsimp [gfWireZero] at hv; omega
  have hbco : ∀ (j : Fin (gfEll n D)) (k : Fin (gfEll n D + 1)), bW j ≠ cW k := fun j k => by
    intro h; have hv := congrArg Fin.val h
    dsimp [bW, cW, gfWireB, gfWireCarry, gfOffCarry, gfOffAcc] at hv
    split_ifs at hv with hj
    · have hlt := (finProdFinEquiv (i, (⟨j.1, hj⟩ : Fin q).rev)).isLt
      dsimp [gfWireX] at hv; omega
    · dsimp [gfWireZero] at hv; omega
  have hcs : ∀ (k : Fin (gfEll n D + 1)) (j : Fin (gfEll n D)), cW k ≠ sW j := fun k j => by
    intro h; have hv := congrArg Fin.val h
    have hs := gfWireAcc_lt_carry n D q a i.succ j
    dsimp [cW, sW, gfWireCarry] at hs hv; omega
  have hsinj : Function.Injective sW := by
    intro u v huv
    have hv := congrArg Fin.val huv; dsimp [sW, gfWireAcc] at hv; exact Fin.ext (by omega)
  have hcinj : Function.Injective cW := by
    intro u v huv
    have hv := congrArg Fin.val huv; dsimp [cW, gfWireCarry] at hv; exact Fin.ext (by omega)
  rippleAddBits aW bW sW cW hab has haco hbs hbco hcs hsinj hcinj (gfEll n D) le_rfl

private lemma gfAccStep_size (n D q a : ℕ) (i : Fin n) :
    (gfAccStep n D q a i).size = 13 * gfEll n D := by
  dsimp [gfAccStep]
  exact rippleAddBits_size _ _ _ _ _ _ _ _ _ _ _ _ (gfEll n D) le_rfl

private noncomputable def gfAccLoop (n D q a : ℕ) : (k : ℕ) → k ≤ n → LayeredCircuit (gfW n D q a)
  | 0, _ => LayeredCircuit.id (gfW n D q a)
  | k + 1, hk => (gfAccLoop n D q a k (by omega)).seq (gfAccStep n D q a ⟨k, hk⟩)

private lemma gfAccLoop_size (n D q a k : ℕ) (hk : k ≤ n) :
    (gfAccLoop n D q a k hk).size = 13 * k * gfEll n D := by
  induction k with
  | zero => simp [gfAccLoop]
  | succ k ih =>
    simp only [gfAccLoop, LayeredCircuit.seq_size, ih (by omega), gfAccStep_size]
    ring

private lemma gfAccLoop_act (n D q a k : ℕ) (hk : k ≤ n) (z : Qubits (gfW n D q a))
    (hzero : z (gfWireZero n D q a) = false)
    (hacc : ∀ (i : Fin (n + 1)) (j : Fin (gfEll n D)), z (gfWireAcc n D q a i j) = false)
    (hcar : ∀ (i : Fin n) (t : Fin (gfEll n D + 1)), z (gfWireCarry n D q a i t) = false) :
    let xBits : Qubits (n * q) := fun t => z ⟨t.1, by have := t.isLt; dsimp [gfW, gfAnc]; omega⟩
    ∃ z' : Qubits (gfW n D q a),
      act (gfAccLoop n D q a k hk).unitary (ket z) = ket z' ∧
      (∀ w : Fin (gfW n D q a), w.1 < gfOffAcc n q a + gfEll n D ∨ gfOffTail n D q a ≤ w.1 →
        z' w = z w) ∧
      (∀ (i : Fin (n + 1)) (j : Fin (gfEll n D)), k < i.1 → z' (gfWireAcc n D q a i j) = false) ∧
      (∀ (i : Fin n) (t : Fin (gfEll n D + 1)), k ≤ i.1 → z' (gfWireCarry n D q a i t) = false) ∧
      bitsToNatLSB (fun j => z' (gfWireAcc n D q a ⟨k, by omega⟩ j)) =
        (∑ t : Fin n, if t.1 < k then bitsToNat (splitReg n q xBits t) else 0) % 2 ^ gfEll n D := by
  intro xBits
  induction k with
  | zero =>
    refine ⟨z, ?_, fun _ _ => rfl, fun i j _ => hacc i j, fun i t _ => hcar i t, ?_⟩
    · simp [gfAccLoop, act_one]
    · have hz0 : (fun j : Fin (gfEll n D) => z (gfWireAcc n D q a ⟨0, Nat.zero_lt_succ n⟩ j)) =
          fun _ => false := funext fun j => hacc ⟨0, Nat.zero_lt_succ n⟩ j
      rw [hz0, ← natToBitsLSB_zero, bitsToNatLSB_natToBitsLSB (Nat.two_pow_pos _)]
      simp
  | succ k ih =>
    rcases ih (by omega) with ⟨z1, h1_act, h1_pres, h1_acc, h1_car, h1_sum⟩
    let ik : Fin n := ⟨k, hk⟩
    have hz1_s : ∀ t : Fin (gfEll n D), z1 (gfWireAcc n D q a ik.succ t) = false := fun t =>
      h1_acc ik.succ t (by simp [ik])
    have hz1_c : ∀ t : Fin (gfEll n D + 1), z1 (gfWireCarry n D q a ik t) = false := fun t =>
      h1_car ik t (by simp [ik])
    rcases rippleAddBits_full _ _ _ _ _ _ _ _ _ _ _ _ z1 hz1_s hz1_c
      with ⟨z2, hstep_act, h2_pres, h2_sum⟩
    have htot : act (gfAccLoop n D q a (k + 1) hk).unitary (ket z) = ket z2 := by
      dsimp only [gfAccLoop]
      rw [LayeredCircuit.seq_unitary, act_mul, h1_act]
      exact hstep_act
    have hdisj_low_s : ∀ (w : Fin (gfW n D q a)) (hw : w.1 < gfOffAcc n q a + gfEll n D ∨
        gfOffTail n D q a ≤ w.1) (t : Fin (gfEll n D)),
        w ≠ gfWireAcc n D q a ik.succ t := fun w hw t => by
      rcases hw with hw1 | hw2
      · intro h; have hval := congrArg Fin.val h; dsimp [gfWireAcc, ik] at hval
        have : gfEll n D ≤ (k + 1) * gfEll n D := Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
        omega
      · have hlt := gfWireAcc_lt_tail n D q a ik.succ t
        intro h; rw [h] at hw2; omega
    have hdisj_low_c : ∀ (w : Fin (gfW n D q a)) (hw : w.1 < gfOffAcc n q a + gfEll n D ∨
        gfOffTail n D q a ≤ w.1) (t : Fin (gfEll n D + 1)),
        w ≠ gfWireCarry n D q a ik t := fun w hw t => by
      rcases hw with hw1 | hw2
      · intro h; have hval := congrArg Fin.val h
        dsimp [gfWireCarry, gfOffCarry] at hval
        have : gfEll n D ≤ (n + 1) * gfEll n D := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
        omega
      · have hlt := gfWireCarry_lt_tail n D q a ik t
        intro h; rw [h] at hw2; omega
    refine ⟨z2, htot, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [h2_pres w (hdisj_low_s w hw) (hdisj_low_c w hw), h1_pres w hw]
    · intro i j hi
      have hne_s' : ∀ t, gfWireAcc n D q a i j ≠ gfWireAcc n D q a ik.succ t := fun t h => by
        have hval := congrArg Fin.val h; dsimp [gfWireAcc, ik] at hval
        have ht := t.isLt
        have : (k + 1 + 1) * gfEll n D ≤ i.1 * gfEll n D := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, one_mul] at this; omega
      have hne_c : ∀ t, gfWireAcc n D q a i j ≠ gfWireCarry n D q a ik t := fun t h => by
        have hlt := gfWireAcc_lt_carry n D q a i j
        have hval := congrArg Fin.val h; dsimp [gfWireCarry] at hval; omega
      rw [h2_pres _ hne_s' hne_c]
      exact h1_acc i j (by omega)
    · intro i t hi
      have hne_s : ∀ s, gfWireCarry n D q a i t ≠ gfWireAcc n D q a ik.succ s := fun s h => by
        have hlt := gfWireAcc_lt_carry n D q a ik.succ s
        have hval := congrArg Fin.val h; dsimp [gfWireCarry] at hval; omega
      have hne_c : ∀ c, gfWireCarry n D q a i t ≠ gfWireCarry n D q a ik c := fun c h => by
        have hval := congrArg Fin.val h; dsimp [gfWireCarry, ik] at hval
        have hc := c.isLt
        have : (k + 1) * (gfEll n D + 1) ≤ i.1 * (gfEll n D + 1) := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, one_mul] at this; omega
      rw [h2_pres _ hne_s hne_c]
      exact h1_car i t (by omega)
    · have hb_val : ∀ j : Fin (gfEll n D), z1 (gfWireB n D q a ik j) =
          if hj : j.1 < q then xBits (finProdFinEquiv (ik, (⟨j.1, hj⟩ : Fin q).rev)) else false := by
        intro j
        dsimp only [gfWireB]
        split_ifs with hj
        · have hlow : (gfWireX n D q a ik (⟨j.1, hj⟩ : Fin q).rev).1 < gfOffAcc n q a + gfEll n D := by
            have := (finProdFinEquiv (ik, (⟨j.1, hj⟩ : Fin q).rev)).isLt
            dsimp [gfWireX, gfOffAcc]; omega
          rw [h1_pres _ (Or.inl hlow)]; rfl
        · have hlow : (gfWireZero n D q a).1 < gfOffAcc n q a + gfEll n D := by
            dsimp [gfWireZero, gfOffAcc]; omega
          rw [h1_pres _ (Or.inl hlow), hzero]
      have hb_bits : bitsToNatLSB (fun j : Fin (gfEll n D) => z1 (gfWireB n D q a ik j)) =
          bitsToNat (splitReg n q xBits ik) % 2 ^ gfEll n D := by
        have hfun : (fun j : Fin (gfEll n D) => z1 (gfWireB n D q a ik j)) =
            fun j : Fin (gfEll n D) =>
              if hj : j.1 < q then (fun t : Fin q => splitReg n q xBits ik t.rev) ⟨j.1, hj⟩ else false := by
          funext j; exact hb_val j
        rw [hfun, bitsToNatLSB_trunc (fun t : Fin q => splitReg n q xBits ik t.rev), bitsToNatLSB_rev]
      change bitsToNatLSB (fun t => z2 (gfWireAcc n D q a ik.succ t)) = _ at h2_sum
      have hsucc_eq : (⟨k + 1, by omega⟩ : Fin (n + 1)) = ik.succ := Fin.ext rfl
      have hcast_eq : (⟨k, hk⟩ : Fin n).castSucc = (⟨k, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
      rw [hsucc_eq, h2_sum, hcast_eq, h1_sum, hb_bits, ← Nat.add_mod]
      congr 1
      change (∑ t : Fin n, if t.1 < k then bitsToNat (splitReg n q xBits t) else 0) +
          bitsToNat (splitReg n q xBits ik) = _
      rw [← Finset.add_sum_erase Finset.univ
          (fun t : Fin n => if t.1 < k + 1 then bitsToNat (splitReg n q xBits t) else 0)
          (Finset.mem_univ ik),
        ← Finset.add_sum_erase Finset.univ
          (fun t : Fin n => if t.1 < k then bitsToNat (splitReg n q xBits t) else 0)
          (Finset.mem_univ ik)]
      have h1 : (if ik.1 < k + 1 then bitsToNat (splitReg n q xBits ik) else 0) =
          bitsToNat (splitReg n q xBits ik) := by simp [ik]
      have h2 : (if ik.1 < k then bitsToNat (splitReg n q xBits ik) else 0) = 0 := by simp [ik]
      have hrest : (∑ t ∈ Finset.univ.erase ik,
          if t.1 < k + 1 then bitsToNat (splitReg n q xBits t) else 0) =
          ∑ t ∈ Finset.univ.erase ik,
            if t.1 < k then bitsToNat (splitReg n q xBits t) else 0 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have hne : t.1 ≠ k := fun h => (Finset.mem_erase.mp ht).1 (Fin.ext h)
        have hiff : t.1 < k + 1 ↔ t.1 < k := by omega
        simp only [hiff]
      rw [h1, h2, zero_add, hrest]
      omega

private noncomputable def goodFlagCompute (n K D q a : ℕ) :
    LayeredCircuit ((n * q + 1 + a) + (1 + gfAnc n D q a)) :=
  let eqS := (multiEqCtrl1 a (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires
    (gfEqSEmb n D q a)
  let cmpD := gfCmpDLoop n D q a n le_rfl
  let andD := (multiEqCtrl1 n (fun _ => true) pauliX pauliX_mem_unitaryGroup).mapWires
    (gfAndDEmb n D q a)
  let acc := gfAccLoop n D q a n le_rfl
  let cmpK := (ltConstCircuit (gfEll n D) K).mapWires (gfCmpKEmb n D q a)
  let cmp2K1 := (ltConstCircuit (gfEll n D) (2 * K + 1)).mapWires (gfCmp2K1Emb n D q a)
  let patComb : Qubits 5 := ![true, true, true, false, true]
  let comb := (multiEqCtrl1 5 patComb pauliX pauliX_mem_unitaryGroup).mapWires
    (gfCombEmb n D q a)
  eqS.seq (cmpD.seq (andD.seq (acc.seq (cmpK.seq (cmp2K1.seq comb)))))

private lemma goodFlagCompute_size (n K D q a : ℕ) :
    (goodFlagCompute n K D q a).size ≤ 162 * (n * (q + gfEll n D) + a + 1) := by
  dsimp only [goodFlagCompute]
  simp only [LayeredCircuit.seq_size, LayeredCircuit.mapWires_size]
  have h1 := multiEqCtrl1_size a (fun _ => false) pauliX pauliX_mem_unitaryGroup
  have h2 := gfCmpDLoop_size n D q a n le_rfl
  have h3 := multiEqCtrl1_size n (fun _ => true) pauliX pauliX_mem_unitaryGroup
  have h4 := gfAccLoop_size n D q a n le_rfl
  have h5 := ltConstCircuit_size (gfEll n D) K
  have h6 := ltConstCircuit_size (gfEll n D) (2 * K + 1)
  have h7 := multiEqCtrl1_size 5 ![true, true, true, false, true] pauliX pauliX_mem_unitaryGroup
  by_cases hn : n = 0
  · subst hn
    have hell0 : gfEll 0 D = 2 := by
      dsimp [gfEll]; rw [Nat.zero_mul, Nat.zero_add, show Nat.clog 2 2 = 1 from by decide]
    rw [hell0] at h5 h6 ⊢
    omega
  · have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn
    have hell_pos : 1 ≤ gfEll n D := by simp [gfEll]
    have hmul_ell : gfEll n D ≤ n * gfEll n D := Nat.le_mul_of_pos_left _ hn_pos
    have hn_ell : n ≤ n * gfEll n D := Nat.le_mul_of_pos_right _ hell_pos
    nlinarith

private lemma goodFlagCompute_implements (n K D q a : ℕ) (z : Qubits (n * q + 1 + a)) :
    ∃ z' : Qubits ((n * q + 1 + a) + (1 + gfAnc n D q a)),
      act (goodFlagCompute n K D q a).unitary (ket (padZero (n * q + 1 + a) (1 + gfAnc n D q a) z)) =
        ket z' ∧
      z' ⟨n * q + 1 + a, by omega⟩ = isGoodBasis53 n q K D a z := by
  let z0 : Qubits (gfW n D q a) := padZero (n * q + 1 + a) (1 + gfAnc n D q a) z
  have hz0_lt : ∀ (w : Fin (gfW n D q a)) (hw : w.1 < n * q + 1 + a),
      z0 w = z ⟨w.1, hw⟩ := fun w hw => by
    have heq : w = Fin.castAdd (1 + gfAnc n D q a) ⟨w.1, hw⟩ := Fin.ext rfl
    dsimp only [z0]; conv_lhs => rw [heq]
    rw [padZero_castAdd]
  have hz0_ge : ∀ w : Fin (gfW n D q a), n * q + 1 + a ≤ w.1 → z0 w = false := fun w hw => by
    have hlt_anc : w.1 - (n * q + 1 + a) < 1 + gfAnc n D q a := by
      have hlt := w.isLt; dsimp [gfW, gfAnc] at hlt ⊢; omega
    have heq : w = Fin.natAdd (n * q + 1 + a) ⟨w.1 - (n * q + 1 + a), hlt_anc⟩ := by
      apply Fin.ext; simp; omega
    dsimp only [z0]; rw [heq, padZero_natAdd]
  -- Step 1: eqS -> computes s == 0^a into gfWireFS
  have hclean_s : ∀ j : Fin a, z0 (gfWireAncS n D q a j) = false := fun j =>
    hz0_ge _ (by dsimp [gfWireAncS]; omega)
  have heq_s := act_triEmb_multiEqCtrl1_ket
    (gfWireS n D q a) (gfWireFS n D q a) (gfWireAncS n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireS] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncS] at hv; omega))
    (fun i => by have := i.isLt; dsimp [gfWireS, gfWireFS]; omega)
    (fun j => by dsimp [gfWireFS, gfWireAncS]; omega)
    (fun _ => false) z0 hclean_s
  let z1 := Function.update z0 (gfWireFS n D q a) (decide (∀ j : Fin a, basisS53 n q a z j = false))
  have hz1_eq : act (((multiEqCtrl1 a (fun _ => false) pauliX pauliX_mem_unitaryGroup).mapWires
      (gfEqSEmb n D q a))).unitary (ket z0) = ket z1 := by
    dsimp only [gfEqSEmb]
    rw [heq_s, hz0_ge _ (by dsimp [gfWireFS]; omega), Bool.false_xor]
    have hin : ∀ j : Fin a, z0 (gfWireS n D q a j) = basisS53 n q a z j := fun j =>
      hz0_lt _ (by dsimp [gfWireS]; have := j.isLt; omega)
    simp only [hin]; rfl
  -- Helper: any wire ≥ n*q + 1 + a + 2 is unchanged from z0 in z1
  have hz1_hi : ∀ w : Fin (gfW n D q a), n * q + 1 + a + 2 ≤ w.1 → z1 w = false := fun w hw => by
    have hne : w ≠ gfWireFS n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFS] at this; omega
    dsimp only [z1]; rw [Function.update_of_ne hne]; exact hz0_ge _ (by omega)
  -- Step 2: cmpD -> computes α_i < D into gfWireFD i
  have hcmpD := gfCmpDLoop_act n D q a n le_rfl z1
    (fun i => hz1_hi _ (by dsimp [gfWireFD]; omega))
    (fun j => hz1_hi _ (by dsimp [gfWireAncCmpQ]; omega))
  let z2 := gfCmpDState n D q a n le_rfl z1
  -- Step 3: andD -> computes ∀ i, α_i < D into gfWireFDAll
  have hclean_and : ∀ i : Fin n, z2 (gfWireAncAndD n D q a i) = false := fun i => by
    dsimp only [z2, gfCmpDState]
    rw [dif_neg (by dsimp [gfWireAncAndD]; omega)]
    exact hz1_hi _ (by dsimp [gfWireAncAndD]; omega)
  have handD := act_triEmb_multiEqCtrl1_ket
    (gfWireFD n D q a) (gfWireFDAll n D q a) (gfWireAncAndD n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireFD] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncAndD] at hv; omega))
    (fun i => by have := i.isLt; dsimp [gfWireFD, gfWireFDAll]; omega)
    (fun j => by dsimp [gfWireFDAll, gfWireAncAndD]; omega)
    (fun _ => true) z2 hclean_and
  let z3 := Function.update z2 (gfWireFDAll n D q a) (decide (∀ i : Fin n, basisDeg53 n q a z i < D))
  have hz3_eq : act (((multiEqCtrl1 n (fun _ => true) pauliX pauliX_mem_unitaryGroup).mapWires
      (gfAndDEmb n D q a))).unitary (ket z2) = ket z3 := by
    dsimp only [gfAndDEmb]
    rw [handD]
    have hz2_tgt : z2 (gfWireFDAll n D q a) = false := by
      dsimp only [z2, gfCmpDState]
      rw [dif_neg (by dsimp [gfWireFDAll]; omega)]
      exact hz1_hi _ (by dsimp [gfWireFDAll]; omega)
    have hin : ∀ i : Fin n, z2 (gfWireFD n D q a i) = decide (basisDeg53 n q a z i < D) := fun i => by
      dsimp only [z2, gfCmpDState]
      rw [dif_pos (by dsimp [gfWireFD]; exact ⟨by omega, by have := i.isLt; omega⟩)]
      have hidx : (⟨(gfWireFD n D q a i).1 - (n * q + 1 + a + 2 + a), by
          dsimp [gfWireFD]; omega⟩ : Fin n) = i := by
        apply Fin.ext; simp [gfWireFD]
      have hx_eq : (fun t : Fin (n * q) => z1 ⟨t.1, by have := t.isLt; dsimp [gfW, gfAnc]; omega⟩) =
          basisX53 n q a z := by
        funext t
        have hne : (⟨t.1, by have := t.isLt; dsimp [gfW, gfAnc]; omega⟩ : Fin (gfW n D q a)) ≠
            gfWireFS n D q a := fun h => by
          have hv := congrArg Fin.val h; have ht := t.isLt; dsimp [gfWireFS] at hv; omega
        dsimp only [z1]; rw [Function.update_of_ne hne, hz0_lt _ (by dsimp; omega)]
        rfl
      rw [hx_eq, hidx]; rfl
    rw [hz2_tgt, Bool.false_xor]
    simp only [hin, decide_eq_true_eq]; rfl
  have hz3_low : ∀ (w : Fin (gfW n D q a)) (hw : w.1 < n * q + 1 + a), z3 w = z ⟨w.1, hw⟩ := fun w hw => by
    have h1 : w ≠ gfWireFDAll n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFDAll] at this; omega
    have h2 : ¬ (n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + n) := by omega
    have h3 : w ≠ gfWireFS n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFS] at this; omega
    dsimp only [z3]; rw [Function.update_of_ne h1]; dsimp only [z2, gfCmpDState]; rw [dif_neg h2]
    dsimp only [z1]; rw [Function.update_of_ne h3]; exact hz0_lt w hw
  have hz3_tail : ∀ w : Fin (gfW n D q a), n * q + 1 + a + 3 + a + n + q ≤ w.1 → z3 w = false := fun w hw => by
    have h1 : w ≠ gfWireFDAll n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFDAll] at this; omega
    have h2 : ¬ (n * q + 1 + a + 2 + a ≤ w.1 ∧ w.1 < n * q + 1 + a + 2 + a + n) := by omega
    dsimp only [z3]; rw [Function.update_of_ne h1]; dsimp only [z2, gfCmpDState]; rw [dif_neg h2]
    exact hz1_hi w (by omega)
  -- Step 4: acc -> computes (∑ basisDeg) % 2^ℓ into acc[n]
  rcases gfAccLoop_act n D q a n le_rfl z3
    (hz3_tail _ (by dsimp [gfWireZero]; omega))
    (fun i j => hz3_tail _ (by dsimp [gfWireAcc, gfOffAcc]; omega))
    (fun i t => hz3_tail _ (by dsimp [gfWireCarry, gfOffCarry, gfOffAcc]; omega))
    with ⟨z4, hz4_eq, hz4_pres, _, _, hz4_sum⟩
  have hz4_tail : ∀ w : Fin (gfW n D q a), gfOffTail n D q a ≤ w.1 → z4 w = false := fun w hw => by
    rw [hz4_pres _ (Or.inr hw)]
    exact hz3_tail w (by dsimp [gfOffTail, gfOffCarry, gfOffAcc] at hw; omega)
  have hacc_val : bitsToNatLSB (fun j => z4 (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩ j)) =
      (∑ i : Fin n, basisDeg53 n q a z i) % 2 ^ gfEll n D := by
    rw [hz4_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos t.isLt]
    have hx_eq : (fun u : Fin (n * q) => z3 ⟨u.1, by have := u.isLt; dsimp [gfW, gfAnc]; omega⟩) =
        basisX53 n q a z := by
      funext u; rw [hz3_low _ (by have hu := u.isLt; dsimp; omega)]; rfl
    rw [hx_eq]; rfl
  -- Step 5: cmpK -> computes acc[n] < K into gfWireFLtK
  have hcmpK := act_triEmb_ltConst_ket (H := K)
    (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩) (gfWireFLtK n D q a) (gfWireAncCmpL n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAcc] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpL] at hv; omega))
    (fun j => by have := gfWireAcc_lt_tail n D q a ⟨n, Nat.lt_succ_self n⟩ j; dsimp [gfWireFLtK]; omega)
    (fun j => by dsimp [gfWireFLtK, gfWireAncCmpL]; omega)
    z4 (fun j => hz4_tail _ (by dsimp [gfWireAncCmpL]; omega))
  let accVal := (∑ i : Fin n, basisDeg53 n q a z i) % 2 ^ gfEll n D
  let z5 := Function.update z4 (gfWireFLtK n D q a) (decide (accVal < K))
  have hz5_eq : act (((ltConstCircuit (gfEll n D) K).mapWires (gfCmpKEmb n D q a))).unitary (ket z4) =
      ket z5 := by
    dsimp only [gfCmpKEmb]
    rw [hcmpK, hz4_tail _ (by dsimp [gfWireFLtK]; omega), Bool.false_xor, hacc_val]
  -- Step 6: cmp2K1 -> computes acc[n] < 2*K+1 into gfWireFLt2K1
  have hclean_2k1 : ∀ j : Fin (gfEll n D), z5 (gfWireAncCmpL n D q a j) = false := fun j => by
    have hne : gfWireAncCmpL n D q a j ≠ gfWireFLtK n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireAncCmpL, gfWireFLtK] at this; omega
    dsimp only [z5]; rw [Function.update_of_ne hne]
    exact hz4_tail _ (by dsimp [gfWireAncCmpL]; omega)
  have hcmp2K1 := act_triEmb_ltConst_ket (H := 2 * K + 1)
    (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩) (gfWireFLt2K1 n D q a) (gfWireAncCmpL n D q a)
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAcc] at hv; omega))
    (fun u v h => Fin.ext (by have hv := congrArg Fin.val h; dsimp [gfWireAncCmpL] at hv; omega))
    (fun j => by have := gfWireAcc_lt_tail n D q a ⟨n, Nat.lt_succ_self n⟩ j; dsimp [gfWireFLt2K1]; omega)
    (fun j => by dsimp [gfWireFLt2K1, gfWireAncCmpL]; omega)
    z5 hclean_2k1
  let z6 := Function.update z5 (gfWireFLt2K1 n D q a) (decide (accVal < 2 * K + 1))
  have hz6_eq : act (((ltConstCircuit (gfEll n D) (2 * K + 1)).mapWires
      (gfCmp2K1Emb n D q a))).unitary (ket z5) = ket z6 := by
    dsimp only [gfCmp2K1Emb]
    rw [hcmp2K1]
    have hne_k : gfWireFLt2K1 n D q a ≠ gfWireFLtK n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFLt2K1, gfWireFLtK] at this; omega
    have hz5_flt2k1 : z5 (gfWireFLt2K1 n D q a) = false := by
      dsimp only [z5]; rw [Function.update_of_ne hne_k]
      exact hz4_tail _ (by dsimp [gfWireFLt2K1]; omega)
    have hin : (fun j : Fin (gfEll n D) => z5 (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩ j)) =
        fun j : Fin (gfEll n D) => z4 (gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩ j) := by
      funext j
      have hne : gfWireAcc n D q a ⟨n, Nat.lt_succ_self n⟩ j ≠ gfWireFLtK n D q a := fun h => by
        have := gfWireAcc_lt_tail n D q a ⟨n, Nat.lt_succ_self n⟩ j
        have hval := congrArg Fin.val h; dsimp [gfWireFLtK] at hval; omega
      dsimp only [z5]; rw [Function.update_of_ne hne]
    rw [hz5_flt2k1, Bool.false_xor, hin, hacc_val]
  -- Step 7: comb -> 5-way AND into gfWireOut
  let patComb : Qubits 5 := ![true, true, true, false, true]
  have hclean_comb : ∀ k : Fin 5,
      z6 (gfCombEmb n D q a (Fin.natAdd 6 k)) = false := fun k => by
    have heq : gfCombEmb n D q a (Fin.natAdd 6 k) = gfWireAncComb n D q a k := by
      apply Fin.ext
      change (gfCombWire n D q a (Fin.natAdd 6 k)).1 = (gfWireAncComb n D q a k).1
      dsimp only [gfCombWire]
      have h6 : (Fin.natAdd 6 k).1 = 6 + k.1 := Fin.val_natAdd 6 k
      have hn0 : (Fin.natAdd 6 k).1 ≠ 0 := by omega
      have hn1 : (Fin.natAdd 6 k).1 ≠ 1 := by omega
      have hn2 : (Fin.natAdd 6 k).1 ≠ 2 := by omega
      have hn3 : (Fin.natAdd 6 k).1 ≠ 3 := by omega
      have hn4 : (Fin.natAdd 6 k).1 ≠ 4 := by omega
      have hn5 : (Fin.natAdd 6 k).1 ≠ 5 := by omega
      rw [if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4, if_neg hn5]
      dsimp [gfWireAncComb]; omega
    have hne_2k1 : gfWireAncComb n D q a k ≠ gfWireFLt2K1 n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireAncComb, gfWireFLt2K1] at this; omega
    have hne_k : gfWireAncComb n D q a k ≠ gfWireFLtK n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireAncComb, gfWireFLtK] at this; omega
    rw [heq]; dsimp only [z6]; rw [Function.update_of_ne hne_2k1]
    dsimp only [z5]; rw [Function.update_of_ne hne_k]
    exact hz4_tail _ (by dsimp [gfWireAncComb]; omega)
  have hcomb := act_mapWires_multiEqCtrl1_pauliX_ket patComb (gfCombEmb n D q a) z6 hclean_comb
  have htot : act (goodFlagCompute n K D q a).unitary (ket z0) =
      ket (Function.update z6 (gfWireOut n D q a)
        (xor (z6 (gfWireOut n D q a)) (decide (∀ i : Fin 5,
          z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨i.1, by omega⟩) = patComb i)))) := by
    dsimp only [goodFlagCompute]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    rw [hz1_eq, hcmpD, hz3_eq, hz4_eq, hz5_eq, hz6_eq, hcomb]
    have htgt : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨5, Nat.lt_succ_self 5⟩ =
        gfWireOut n D q a := rfl
    rw [htgt]
  refine ⟨_, htot, ?_⟩
  have hw_out_eq : (⟨n * q + 1 + a, by omega⟩ : Fin ((n * q + 1 + a) + (1 + gfAnc n D q a))) =
      gfWireOut n D q a := rfl
  rw [hw_out_eq, Function.update_self]
  have hlow_z6 : ∀ (w : Fin (gfW n D q a)), w.1 < n * q + 1 + a + 2 + a → z6 w = z3 w := fun w hw => by
    have hne1 : w ≠ gfWireFLt2K1 n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFLt2K1, gfOffTail, gfOffCarry, gfOffAcc] at this; omega
    have hne2 : w ≠ gfWireFLtK n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFLtK, gfOffTail, gfOffCarry, gfOffAcc] at this; omega
    dsimp only [z6]; rw [Function.update_of_ne hne1]
    dsimp only [z5]; rw [Function.update_of_ne hne2]
    exact hz4_pres w (Or.inl (by dsimp [gfOffAcc]; omega))
  have hz6_out : z6 (gfWireOut n D q a) = false := by
    rw [hlow_z6 _ (by dsimp [gfWireOut]; omega)]
    have h1 : gfWireOut n D q a ≠ gfWireFDAll n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireOut, gfWireFDAll] at this; omega
    have h2 : ¬ (n * q + 1 + a + 2 + a ≤ (gfWireOut n D q a).1 ∧
        (gfWireOut n D q a).1 < n * q + 1 + a + 2 + a + n) := by dsimp [gfWireOut]; omega
    have h3 : gfWireOut n D q a ≠ gfWireFS n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireOut, gfWireFS] at this; omega
    dsimp only [z3]; rw [Function.update_of_ne h1]; dsimp only [z2, gfCmpDState]; rw [dif_neg h2]
    dsimp only [z1]; rw [Function.update_of_ne h3]; exact hz0_ge _ (by dsimp [gfWireOut]; omega)
  rw [hz6_out, Bool.false_xor]
  have hin0 : z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(0 : Fin 5).1, by omega⟩) =
      basisY53 n q a z := by
    have hw : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(0 : Fin 5).1, by omega⟩ =
        gfWireY n D q a := rfl
    rw [hw, hlow_z6 _ (by dsimp [gfWireY]; omega), hz3_low _ (by dsimp [gfWireY]; omega)]; rfl
  have hin1 : z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(1 : Fin 5).1, by omega⟩) =
      decide (∀ j : Fin a, basisS53 n q a z j = false) := by
    have hw : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(1 : Fin 5).1, by omega⟩ =
        gfWireFS n D q a := rfl
    rw [hw, hlow_z6 _ (by dsimp [gfWireFS]; omega)]
    have h1 : gfWireFS n D q a ≠ gfWireFDAll n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFS, gfWireFDAll] at this; omega
    have h2 : ¬ (n * q + 1 + a + 2 + a ≤ (gfWireFS n D q a).1 ∧
        (gfWireFS n D q a).1 < n * q + 1 + a + 2 + a + n) := by dsimp [gfWireFS]; omega
    dsimp only [z3]; rw [Function.update_of_ne h1]; dsimp only [z2, gfCmpDState]; rw [dif_neg h2]
    dsimp only [z1]; rw [Function.update_self]
  have hin2 : z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(2 : Fin 5).1, by omega⟩) =
      decide (∀ i : Fin n, basisDeg53 n q a z i < D) := by
    have hw : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(2 : Fin 5).1, by omega⟩ =
        gfWireFDAll n D q a := rfl
    rw [hw]
    have hne1 : gfWireFDAll n D q a ≠ gfWireFLt2K1 n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFDAll, gfWireFLt2K1, gfOffTail, gfOffCarry, gfOffAcc] at this; omega
    have hne2 : gfWireFDAll n D q a ≠ gfWireFLtK n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFDAll, gfWireFLtK, gfOffTail, gfOffCarry, gfOffAcc] at this; omega
    have hlow : (gfWireFDAll n D q a).1 < gfOffAcc n q a + gfEll n D := by
      dsimp [gfWireFDAll, gfOffAcc]; omega
    dsimp only [z6]; rw [Function.update_of_ne hne1]; dsimp only [z5]; rw [Function.update_of_ne hne2]
    rw [hz4_pres _ (Or.inl hlow)]; dsimp only [z3]; rw [Function.update_self]
  have hin3 : z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(3 : Fin 5).1, by omega⟩) =
      decide (accVal < K) := by
    have hw : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(3 : Fin 5).1, by omega⟩ =
        gfWireFLtK n D q a := rfl
    rw [hw]
    have hne1 : gfWireFLtK n D q a ≠ gfWireFLt2K1 n D q a := fun h => by
      have := congrArg Fin.val h; dsimp [gfWireFLtK, gfWireFLt2K1] at this; omega
    dsimp only [z6]; rw [Function.update_of_ne hne1]; dsimp only [z5]; rw [Function.update_self]
  have hin4 : z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(4 : Fin 5).1, by omega⟩) =
      decide (accVal < 2 * K + 1) := by
    have hw : ((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨(4 : Fin 5).1, by omega⟩ =
        gfWireFLt2K1 n D q a := rfl
    rw [hw]; dsimp only [z6]; rw [Function.update_self]
  have hcomb_iff :
      (∀ i : Fin 5,
        z6 (((Fin.castAddEmb 5).trans (gfCombEmb n D q a)) ⟨i.1, by omega⟩) = patComb i) ↔
      (basisY53 n q a z = true ∧
       (∀ j : Fin a, basisS53 n q a z j = false) ∧
       (∀ i : Fin n, basisDeg53 n q a z i < D) ∧
       ¬ (accVal < K) ∧ accVal < 2 * K + 1) := by
    constructor
    · intro h
      have h0 := h 0; rw [hin0] at h0
      have h1 := h 1; rw [hin1] at h1
      have h2 := h 2; rw [hin2] at h2
      have h3 := h 3; rw [hin3] at h3
      have h4 := h 4; rw [hin4] at h4
      have hy : basisY53 n q a z = true := h0
      have hs : ∀ j : Fin a, basisS53 n q a z j = false :=
        decide_eq_true_iff.mp h1
      have hd : ∀ i : Fin n, basisDeg53 n q a z i < D :=
        decide_eq_true_iff.mp h2
      have hk1 : ¬ (accVal < K) :=
        decide_eq_false_iff_not.mp h3
      have hk2 : accVal < 2 * K + 1 :=
        decide_eq_true_iff.mp h4
      exact ⟨hy, hs, hd, hk1, hk2⟩
    · rintro ⟨hy, hs, hd, hk1, hk2⟩ i
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by fin_cases i <;> simp
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · rw [hin0]; exact hy
      · rw [hin1]; exact decide_eq_true hs
      · rw [hin2]; exact decide_eq_true hd
      · rw [hin3]; exact decide_eq_false hk1
      · rw [hin4]; exact decide_eq_true hk2
  apply Bool.eq_iff_iff.mpr
  dsimp only [isGoodBasis53]
  simp only [decide_eq_true_eq, hcomb_iff]
  constructor
  · rintro ⟨hy, hs, hd, hk1, hk2⟩
    have hlt_pow : ∑ i : Fin n, basisDeg53 n q a z i < 2 ^ gfEll n D :=
      degree_sum_lt_pow_ell n D (basisDeg53 n q a z) hd
    have hacc_eq : accVal = ∑ i : Fin n, basisDeg53 n q a z i :=
      Nat.mod_eq_of_lt hlt_pow
    rw [hacc_eq] at hk1 hk2
    exact ⟨hy, hs, hd, by omega, by omega⟩
  · rintro ⟨hy, hs, hd, hk1, hk2⟩
    have hlt_pow : ∑ i : Fin n, basisDeg53 n q a z i < 2 ^ gfEll n D :=
      degree_sum_lt_pow_ell n D (basisDeg53 n q a z) hd
    have hacc_eq : accVal = ∑ i : Fin n, basisDeg53 n q a z i :=
      Nat.mod_eq_of_lt hlt_pow
    rw [hacc_eq]
    exact ⟨hy, hs, hd, by omega, by omega⟩

noncomputable def goodMarkerCircuit (n K D q a : ℕ) :
    Circuit gates12 (((n * q + 1 + a) + 1) + (1 + gfAnc n D q a)) :=
  (markerGateOfFlag (goodFlagCompute n K D q a)).toCircuit

noncomputable def goodReflectCircuit (n K D q a : ℕ) :
    Circuit gates12 ((n * q + 1 + a) + (1 + gfAnc n D q a)) :=
  (phaseGateOfFlag (goodFlagCompute n K D q a)).toCircuit

lemma goodMarkerCircuit_size (n K D q a : ℕ) :
    (goodMarkerCircuit n K D q a).length ≤ 325 * (n * (q + gfEll n D) + a + 1) := by
  change (markerGateOfFlag (goodFlagCompute n K D q a)).size ≤ _
  rw [markerGateOfFlag_size]
  have h1 := goodFlagCompute_size n K D q a
  omega

lemma goodMarkerCircuit_act (n K D q a : ℕ) (z : Qubits (n * q + 1 + a)) (b : Bool) :
    act (goodMarkerCircuit n K D q a).unitary
        (ket (Fin.append (Fin.snoc (α := fun _ => Bool) z b)
          (fun _ : Fin (1 + gfAnc n D q a) => false))) =
      ket (Fin.append (Fin.snoc (α := fun _ => Bool) z (xor b (isGoodBasis53 n q K D a z)))
        (fun _ : Fin (1 + gfAnc n D q a) => false)) :=
  markerGateOfFlag_implements (goodFlagCompute n K D q a) (isGoodBasis53 n q K D a)
    (goodFlagCompute_implements n K D q a) z b

lemma goodReflectCircuit_size (n K D q a : ℕ) :
    (goodReflectCircuit n K D q a).length ≤ 325 * (n * (q + gfEll n D) + a + 1) := by
  change (phaseGateOfFlag (goodFlagCompute n K D q a)).size ≤ _
  rw [phaseGateOfFlag_size]
  have h1 := goodFlagCompute_size n K D q a
  omega

lemma goodReflectCircuit_act (n K D q a : ℕ) (z : Qubits (n * q + 1 + a)) :
    act (goodReflectCircuit n K D q a).unitary
        (ket (Fin.append z (fun _ : Fin (1 + gfAnc n D q a) => false))) =
      (if isGoodBasis53 n q K D a z = true then (-1 : ℂ) else 1) •
        ket (Fin.append z (fun _ : Fin (1 + gfAnc n D q a) => false)) := by
  have himp := phaseGateOfFlag_implements (goodFlagCompute n K D q a)
    (isGoodBasis53 n q K D a) (goodFlagCompute_implements n K D q a)
  change act (phaseGateOfFlag (goodFlagCompute n K D q a)).unitary
    (ket (padZero (n * q + 1 + a) (1 + gfAnc n D q a) z)) = _
  rw [act_ket_of_implementsOnClean himp z, Finset.sum_eq_single z]
  · simp [diagPhaseMat, padZero_eq_append]
  · intro y _ hy; simp [diagPhaseMat, hy]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def bandCircuits53Impl : BandCircuits53 where
  C_circ := 350
  hC_circ_pos := by norm_num
  ancMarker := fun n _ D q a => 1 + gfAnc n D q a
  goodMarkerCircuit := goodMarkerCircuit
  goodMarker_size := fun n K D q a => by
    have h : (goodMarkerCircuit n K D q a).length ≤ 325 * (n * (q + gfEll n D) + a + 1) :=
      goodMarkerCircuit_size n K D q a
    have hR : ((goodMarkerCircuit n K D q a).length : ℝ) ≤
        325 * ((n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1) := by
      exact_mod_cast h
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1 := by
      positivity
    linarith
  goodMarker_act := goodMarkerCircuit_act
  ancGoodRefl := fun n _ D q a => 1 + gfAnc n D q a
  goodReflectCircuit := goodReflectCircuit
  goodReflect_size := fun n K D q a => by
    have h : (goodReflectCircuit n K D q a).length ≤ 325 * (n * (q + gfEll n D) + a + 1) :=
      goodReflectCircuit_size n K D q a
    have hR : ((goodReflectCircuit n K D q a).length : ℝ) ≤
        325 * ((n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1) := by
      exact_mod_cast h
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) : ℝ) + 1) + (a : ℝ) + 1 := by
      positivity
    linarith
  goodReflect_act := goodReflectCircuit_act
  ancZeroRefl := fun n q a => 1 + (n * q + 1 + a)
  zeroReflectCircuit := zeroReflectCircuit
  zeroReflect_size := fun n q a => by
    have h := zeroReflectCircuit_size n q a
    have hR : ((zeroReflectCircuit n q a).length : ℝ) ≤ 49 * ((n : ℝ) * (q : ℝ) + (a : ℝ) + 1) := by
      exact_mod_cast h
    have hnn : (0 : ℝ) ≤ (n : ℝ) * (q : ℝ) + (a : ℝ) + 1 := by positivity
    linarith
  zeroReflect_act := zeroReflectCircuit_act
  ancFirstHitSwap := fun R _ => 2 * R
  firstHitSwapCircuit := firstHitSwapCircuit
  firstHitSwap_size := fun R m_reg => by
    have h := firstHitSwapCircuit_size R m_reg
    have hR : ((firstHitSwapCircuit R m_reg).length : ℝ) ≤ 24 * (R : ℝ) * ((m_reg : ℝ) + 1) := by
      exact_mod_cast h
    have hnn : (0 : ℝ) ≤ (R : ℝ) * ((m_reg : ℝ) + 1) := by positivity
    linarith
  firstHitSwap_act := firstHitSwapCircuit_act

end BandCircuits53Work

theorem solution : Nonempty QuantumLTF.Membership.Supplement.BandCircuits53 :=
  ⟨BandCircuits53Work.bandCircuits53Impl⟩
