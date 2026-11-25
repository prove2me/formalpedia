-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-25T04:08:01.829602+00:00
-- url     : https://prove2.me/submissions/7438dca1-5c43-404d-ab11-e4a5502eb774
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Theorems.Thm_QuantumLTF_Membership_Supplement_band_channel_algebra_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_occupation_to_nsil_54
import Theorems.Thm_QuantumLTF_Membership_Supplement_nsil_symmetrize_54

set_option autoImplicit false

namespace Aux_Thm54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open Thm49Primitives

/-! ### 1. Base Case `n = 0` -/

lemma theorem_5_4_n_zero {C : ℝ} (hC : 0 < C) (K' : ℕ) {K D q : ℕ}
    (hK : 1 ≤ K) (_hD : 2 * K + 1 ≤ D) (_hq : D ≤ 2 ^ q) :
    ∃ (s e r : ℕ) (V : Circuit gates12 (0 * q + e)) (W : Qubits r → Circuit gates12 (0 * q + e))
      (meas : Fin r ↪ Fin (0 * q + e)) (out : Fin (K * s) ↪ Fin (0 * q + e)),
      0 ≤ 2 ^ s ∧ (r : ℝ) ≤ C * K ∧
      (∀ t : Qubits r, ((V.size + (W t).size : ℕ) : ℝ) ≤
        C * 0 * (Real.log (2 ^ q) + Real.log (0 * D)) +
          C * (0 + K * Real.log (0 + 1)) * Real.log ((K + 1) * (0 + 1)) ^ K') ∧
      ∀ w : EuclideanSpace ℝ (Fin 0), ‖w‖ = 1 →
        measChannelOut V.unitary (fun t => (W t).unitary) meas out
          (padKet e (bandKet 0 q K w)) = dirTensorPow s K w := by
  let meas : Fin 0 ↪ Fin (0 * q + 0) :=
    ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  let out : Fin (K * 0) ↪ Fin (0 * q + 0) :=
    ⟨fun i => absurd i.isLt (by omega), fun i => absurd i.isLt (by omega)⟩
  refine ⟨0, 0, 0, [], fun _ => [], meas, out, by norm_num, ?_, ?_, ?_⟩
  · have : (0 : ℝ) ≤ C * (K : ℝ) := by positivity
    simpa using this
  · intro t
    simp [Circuit.size]
  · intro w hw
    have hw0 : w = 0 := Subsingleton.elim w 0
    rw [hw0, norm_zero] at hw
    norm_num at hw

/-! ### 2. `swapApp` Action & `W(t)` Register-Compaction Circuit -/

lemma swapApp_unitary_eq_permMat {m : ℕ} (u v : Fin m) (hne : u ≠ v) :
    Circuit.unitary ([swapApp u v hne] : Circuit gates12 m) =
      permMat (fun z : Qubits m => z ∘ Equiv.swap u v) := by
  ext y z
  simp only [Circuit.unitary, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.prod_cons, List.prod_nil, mul_one]
  change embedOp (swapApp u v hne).gate.mat (swapApp u v hne).wires y z =
    if y = z ∘ Equiv.swap u v then 1 else 0
  rw [swapApp, embedOp_gate2App_entry]
  by_cases hyz : y = z ∘ Equiv.swap u v
  · rw [if_pos hyz]
    have hoff : ∀ a : Fin m, a ≠ u → a ≠ v → y a = z a := by
      intro a hau hav
      rw [hyz, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hau hav]
    rw [if_pos hoff, hyz, Function.comp_apply, Function.comp_apply,
      Equiv.swap_apply_left, Equiv.swap_apply_right]
    simp [swapGate]
  · rw [if_neg hyz]
    split_ifs with hoff
    · by_cases huv : y u = z v ∧ y v = z u
      · exfalso; apply hyz; funext a
        by_cases hau : a = u
        · subst hau; simp [huv.1]
        · by_cases hav : a = v
          · subst hav; simp [huv.2]
          · simp [hoff a hau hav, Equiv.swap_apply_of_ne_of_ne hau hav]
      · simp [swapGate, huv]
    · rfl

lemma permMat_mul_permMat {ι : Type*} [Fintype ι] [DecidableEq ι] (g f : ι → ι) :
    permMat g * permMat f = permMat (g ∘ f) := by
  ext y z
  simp only [Matrix.mul_apply, permMat, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (f z)]
  · simp
  · intro w _ hw; simp [hw]
  · intro h; exact absurd (Finset.mem_univ _) h

def partWire54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (j : Fin (2 * K)) (c : Fin s) : Fin m :=
  partEmb (finProdFinEquiv (j, c))

lemma partWire54_inj {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    {j₁ j₂ : Fin (2 * K)} {c₁ c₂ : Fin s}
    (h : partWire54 partEmb j₁ c₁ = partWire54 partEmb j₂ c₂) :
    j₁ = j₂ ∧ c₁ = c₂ := by
  have h1 := finProdFinEquiv.injective (partEmb.injective h)
  exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

def outEmb54 (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m) : Fin (K * s) ↪ Fin m where
  toFun p := partEmb ⟨p.1, by nlinarith [p.isLt]⟩
  inj' p₁ p₂ h := Fin.ext (by
    have := congrArg Fin.val (partEmb.injective h)
    exact this)

lemma outEmb54_finProd {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (k : Fin K) (c : Fin s) :
    outEmb54 K s m partEmb (finProdFinEquiv (k, c)) =
      partWire54 partEmb ⟨k.1, by omega⟩ c := by
  change partEmb ⟨(finProdFinEquiv (k, c)).1, _⟩ =
    partEmb (finProdFinEquiv (⟨k.1, by omega⟩, c))
  congr 1

noncomputable def permutePart54 (K s m : ℕ) (partEmb : Fin (2 * K * s) ↪ Fin m)
    (π : Equiv.Perm (Fin (2 * K))) (z : Qubits m) : Qubits m :=
  fun w => open Classical in
    if h : ∃ p : Fin (2 * K) × Fin s, partWire54 partEmb p.1 p.2 = w then
      let p := Classical.choose h
      z (partWire54 partEmb (π p.1) p.2)
    else z w

lemma permutePart54_out {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (π : Equiv.Perm (Fin (2 * K))) (z : Qubits m)
    {w : Fin m} (hw : w ∉ Set.range partEmb) :
    permutePart54 K s m partEmb π z w = z w := by
  classical
  have hnot : ¬ ∃ p : Fin (2 * K) × Fin s, partWire54 partEmb p.1 p.2 = w := by
    rintro ⟨p, hp⟩
    exact hw ⟨finProdFinEquiv p, hp⟩
  dsimp only [permutePart54]
  rw [dif_neg hnot]

lemma permutePart54_in {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (π : Equiv.Perm (Fin (2 * K))) (z : Qubits m)
    (j : Fin (2 * K)) (c : Fin s) :
    permutePart54 K s m partEmb π z (partWire54 partEmb j c) =
      z (partWire54 partEmb (π j) c) := by
  classical
  have hex : ∃ p : Fin (2 * K) × Fin s, partWire54 partEmb p.1 p.2 = partWire54 partEmb j c :=
    ⟨(j, c), rfl⟩
  dsimp only [permutePart54]
  rw [dif_pos hex]
  have hp := partWire54_inj partEmb (Classical.choose_spec hex)
  rw [hp.1, hp.2]

lemma permutePart54_one {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m) (z : Qubits m) :
    permutePart54 K s m partEmb 1 z = z := by
  funext w
  by_cases hw : w ∈ Set.range partEmb
  · obtain ⟨q, rfl⟩ := hw
    obtain ⟨⟨j, c⟩, hq⟩ := finProdFinEquiv.surjective q
    rw [← hq]
    exact permutePart54_in partEmb 1 z j c
  · exact permutePart54_out partEmb 1 z hw

lemma permutePart54_comp {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (π₁ π₂ : Equiv.Perm (Fin (2 * K))) (z : Qubits m) :
    permutePart54 K s m partEmb π₂ (permutePart54 K s m partEmb π₁ z) =
      permutePart54 K s m partEmb (π₁ * π₂) z := by
  funext w
  by_cases hw : w ∈ Set.range partEmb
  · obtain ⟨q, rfl⟩ := hw
    obtain ⟨⟨j, c⟩, hq⟩ := finProdFinEquiv.surjective q
    rw [← hq]
    change permutePart54 K s m partEmb π₂ (permutePart54 K s m partEmb π₁ z) (partWire54 partEmb j c) =
      permutePart54 K s m partEmb (π₁ * π₂) z (partWire54 partEmb j c)
    rw [permutePart54_in, permutePart54_in, permutePart54_in]
    rfl
  · rw [permutePart54_out _ _ _ hw, permutePart54_out _ _ _ hw, permutePart54_out _ _ _ hw]

private noncomputable def permSomeC54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (cs : List (Fin s)) (z : Qubits m) : Qubits m :=
  fun w => open Classical in
    if h : ∃ c : Fin s, c ∈ cs ∧
        (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) then
      let c := Classical.choose h
      if w = partWire54 partEmb a c then z (partWire54 partEmb b c)
      else z (partWire54 partEmb a c)
    else z w

private def swapSomeC54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (hab : a ≠ b) (cs : List (Fin s)) : Circuit gates12 m :=
  cs.map fun c =>
    swapApp (partWire54 partEmb a c) (partWire54 partEmb b c)
      (fun h => hab (partWire54_inj partEmb h).1)

private lemma swapSomeC54_unitary {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (hab : a ≠ b) (cs : List (Fin s)) (hnd : cs.Nodup) :
    Circuit.unitary (swapSomeC54 partEmb a b hab cs) =
      permMat (permSomeC54 partEmb a b cs) := by
  classical
  induction cs with
  | nil =>
    have hid : permSomeC54 partEmb a b [] = id := by
      funext z w
      have hnot : ¬ ∃ c : Fin s, c ∈ ([] : List (Fin s)) ∧
          (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) := by
        rintro ⟨c, hc, _⟩; exact List.not_mem_nil hc
      dsimp only [permSomeC54]
      rw [dif_neg hnot]
      rfl
    rw [hid]
    ext y z
    simp [swapSomeC54, Circuit.unitary, permMat, Matrix.one_apply]
  | cons c₀ cs' ih =>
    rw [List.nodup_cons] at hnd
    have hcons : swapSomeC54 partEmb a b hab (c₀ :: cs') =
        [swapApp (partWire54 partEmb a c₀) (partWire54 partEmb b c₀)
          (fun h => hab (partWire54_inj partEmb h).1)] ++ swapSomeC54 partEmb a b hab cs' := rfl
    rw [hcons, circuit_unitary_append, ih hnd.2, swapApp_unitary_eq_permMat, permMat_mul_permMat]
    congr 1
    funext z w
    dsimp only [Function.comp_apply, permSomeC54]
    let u₀ := partWire54 partEmb a c₀
    let v₀ := partWire54 partEmb b c₀
    have hnot_u0 : ¬ ∃ c : Fin s, c ∈ cs' ∧ (u₀ = partWire54 partEmb a c ∨ u₀ = partWire54 partEmb b c) := by
      rintro ⟨c, hc, h | h⟩
      · have := (partWire54_inj partEmb h).2; subst this; exact hnd.1 hc
      · exact hab (partWire54_inj partEmb h).1
    have hnot_v0 : ¬ ∃ c : Fin s, c ∈ cs' ∧ (v₀ = partWire54 partEmb a c ∨ v₀ = partWire54 partEmb b c) := by
      rintro ⟨c, hc, h | h⟩
      · exact hab.symm (partWire54_inj partEmb h).1
      · have := (partWire54_inj partEmb h).2; subst this; exact hnd.1 hc
    by_cases hw_cs' : ∃ c : Fin s, c ∈ cs' ∧ (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c)
    · have hw_all : ∃ c : Fin s, c ∈ c₀ :: cs' ∧ (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) := by
        obtain ⟨c, hc, h⟩ := hw_cs'; exact ⟨c, List.mem_cons_of_mem c₀ hc, h⟩
      rw [dif_pos hw_cs', dif_pos hw_all]
      obtain ⟨hc1, hc1_or⟩ := Classical.choose_spec hw_cs'
      obtain ⟨hc2, hc2_or⟩ := Classical.choose_spec hw_all
      set c1 := Classical.choose hw_cs'
      set c2 := Classical.choose hw_all
      have hc12 : c1 = c2 := by
        rcases hc1_or with h1 | h1 <;> rcases hc2_or with h2 | h2
        · exact (partWire54_inj partEmb (h1.symm.trans h2)).2
        · exact absurd (partWire54_inj partEmb (h1.symm.trans h2)).1 hab
        · exact absurd (partWire54_inj partEmb (h1.symm.trans h2)).1 hab.symm
        · exact (partWire54_inj partEmb (h1.symm.trans h2)).2
      rw [← hc12]
      have hne_c0 : c1 ≠ c₀ := fun h => hnd.1 (h ▸ hc1)
      split_ifs with hwa
      · have hne1 : partWire54 partEmb b c1 ≠ u₀ := fun h => hne_c0 (partWire54_inj partEmb h).2
        have hne2 : partWire54 partEmb b c1 ≠ v₀ := fun h => hne_c0 (partWire54_inj partEmb h).2
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      · have hne1 : partWire54 partEmb a c1 ≠ u₀ := fun h => hne_c0 (partWire54_inj partEmb h).2
        have hne2 : partWire54 partEmb a c1 ≠ v₀ := fun h => hne_c0 (partWire54_inj partEmb h).2
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    · rw [dif_neg hw_cs']
      by_cases hwu : w = u₀
      · have hw_all : ∃ c : Fin s, c ∈ c₀ :: cs' ∧ (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) :=
          ⟨c₀, List.mem_cons_self, Or.inl hwu⟩
        rw [dif_pos hw_all]
        obtain ⟨hc2, hc2_or⟩ := Classical.choose_spec hw_all
        set c2 := Classical.choose hw_all
        have hc2_eq : c2 = c₀ := by
          rcases hc2_or with h2 | h2
          · exact (partWire54_inj partEmb (h2.symm.trans hwu)).2
          · exact absurd (partWire54_inj partEmb (hwu.symm.trans h2)).1 hab
        rw [hc2_eq, if_pos hwu, hwu]
        change (z ∘ Equiv.swap u₀ v₀) u₀ = z v₀
        simp
      · by_cases hwv : w = v₀
        · have hw_all : ∃ c : Fin s, c ∈ c₀ :: cs' ∧ (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) :=
            ⟨c₀, List.mem_cons_self, Or.inr hwv⟩
          rw [dif_pos hw_all]
          obtain ⟨hc2, hc2_or⟩ := Classical.choose_spec hw_all
          set c2 := Classical.choose hw_all
          have hc2_eq : c2 = c₀ := by
            rcases hc2_or with h2 | h2
            · exact absurd (partWire54_inj partEmb (hwv.symm.trans h2)).1 hab.symm
            · exact (partWire54_inj partEmb (h2.symm.trans hwv)).2
          have hne_wa : w ≠ partWire54 partEmb a c2 := by
            rw [hc2_eq, hwv]; intro h; exact hab.symm (partWire54_inj partEmb h).1
          rw [hc2_eq] at hne_wa
          rw [hc2_eq, if_neg hne_wa, hwv]
          change (z ∘ Equiv.swap u₀ v₀) v₀ = z u₀
          simp
        · have hw_not_all : ¬ ∃ c : Fin s, c ∈ c₀ :: cs' ∧
              (w = partWire54 partEmb a c ∨ w = partWire54 partEmb b c) := by
            rintro ⟨c, hc, h⟩
            rcases List.mem_cons.mp hc with rfl | hc'
            · rcases h with h | h <;> contradiction
            · exact hw_cs' ⟨c, hc', h⟩
          rw [dif_neg hw_not_all]
          change (z ∘ Equiv.swap u₀ v₀) w = z w
          rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hwu hwv]

def swapRegCircuit54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (hab : a ≠ b) : Circuit gates12 m :=
  swapSomeC54 partEmb a b hab (List.finRange s)

lemma swapRegCircuit54_size {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (hab : a ≠ b) :
    (swapRegCircuit54 partEmb a b hab).size = s := by
  simp [swapRegCircuit54, swapSomeC54, Circuit.size]

lemma swapRegCircuit54_unitary {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (a b : Fin (2 * K)) (hab : a ≠ b) :
    (swapRegCircuit54 partEmb a b hab).unitary =
      permMat (permutePart54 K s m partEmb (Equiv.swap a b)) := by
  rw [swapRegCircuit54, swapSomeC54_unitary partEmb a b hab (List.finRange s) (List.nodup_finRange s)]
  congr 1
  funext z w
  by_cases hw : w ∈ Set.range partEmb
  · obtain ⟨q, rfl⟩ := hw
    obtain ⟨⟨j, c⟩, hq⟩ := finProdFinEquiv.surjective q
    rw [← hq]
    change permSomeC54 partEmb a b (List.finRange s) z (partWire54 partEmb j c) =
      permutePart54 K s m partEmb (Equiv.swap a b) z (partWire54 partEmb j c)
    rw [permutePart54_in]
    classical
    dsimp only [permSomeC54]
    by_cases hja : j = a
    · rw [hja] at *
      have hex : ∃ c' : Fin s, c' ∈ List.finRange s ∧
          (partWire54 partEmb a c = partWire54 partEmb a c' ∨
            partWire54 partEmb a c = partWire54 partEmb b c') :=
        ⟨c, List.mem_finRange c, Or.inl rfl⟩
      rw [dif_pos hex]
      obtain ⟨_, hc'_or⟩ := Classical.choose_spec hex
      have hc' : Classical.choose hex = c := by
        rcases hc'_or with h | h
        · exact (partWire54_inj partEmb h).2.symm
        · exact absurd (partWire54_inj partEmb h).1 hab
      rw [hc', if_pos rfl, Equiv.swap_apply_left]
    · by_cases hjb : j = b
      · rw [hjb] at *
        have hex : ∃ c' : Fin s, c' ∈ List.finRange s ∧
            (partWire54 partEmb b c = partWire54 partEmb a c' ∨
              partWire54 partEmb b c = partWire54 partEmb b c') :=
          ⟨c, List.mem_finRange c, Or.inr rfl⟩
        rw [dif_pos hex]
        obtain ⟨_, hc'_or⟩ := Classical.choose_spec hex
        have hc' : Classical.choose hex = c := by
          rcases hc'_or with h | h
          · exact absurd (partWire54_inj partEmb h).1 hab.symm
          · exact (partWire54_inj partEmb h).2.symm
        have hne : partWire54 partEmb b c ≠ partWire54 partEmb a c := fun h =>
          hab.symm (partWire54_inj partEmb h).1
        rw [hc', if_neg hne, Equiv.swap_apply_right]
      · have hnot : ¬ ∃ c' : Fin s, c' ∈ List.finRange s ∧
            (partWire54 partEmb j c = partWire54 partEmb a c' ∨
              partWire54 partEmb j c = partWire54 partEmb b c') := by
          rintro ⟨c', _, h | h⟩
          · exact hja (partWire54_inj partEmb h).1
          · exact hjb (partWire54_inj partEmb h).1
        rw [dif_neg hnot, Equiv.swap_apply_of_ne_of_ne hja hjb]
  · rw [permutePart54_out _ _ _ hw]
    classical
    have hnot : ¬ ∃ c' : Fin s, c' ∈ List.finRange s ∧
        (w = partWire54 partEmb a c' ∨ w = partWire54 partEmb b c') := by
      rintro ⟨c', _, rfl | rfl⟩
      · exact hw ⟨finProdFinEquiv (a, c'), rfl⟩
      · exact hw ⟨finProdFinEquiv (b, c'), rfl⟩
    dsimp only [permSomeC54]
    rw [dif_neg hnot]

def compactPairs54 (K : ℕ) (t : Qubits (2 * K)) :
    List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 } :=
  if _ : K ≤ (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card then
    let badL : Finset (Fin K) := Finset.univ.filter fun i : Fin K => t ⟨i.1, by omega⟩ = true
    let goodR : Finset (Fin K) := Finset.univ.filter fun i : Fin K => t ⟨K + i.1, by omega⟩ = false
    let bs : List (Fin K) := badL.sort (· ≤ ·)
    let gs : List (Fin K) := (goodR.sort (· ≤ ·)).take badL.card
    (bs.zip gs).map fun p =>
      ⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), by
        intro h
        have hv := congrArg Fin.val h
        dsimp at hv
        omega⟩
  else []

def compactW54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K)) : Circuit gates12 m :=
  ((compactPairs54 K t).map fun p => swapRegCircuit54 partEmb p.1.1 p.1.2 p.2).flatten

def permOfPairs54 (K : ℕ)
    (ps : List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 }) : Equiv.Perm (Fin (2 * K)) :=
  (ps.map fun p => Equiv.swap p.1.1 p.1.2).prod

def compactPerm54 (K : ℕ) (t : Qubits (2 * K)) : Equiv.Perm (Fin (2 * K)) :=
  permOfPairs54 K (compactPairs54 K t)

lemma compactPairs54_length_le (K : ℕ) (t : Qubits (2 * K)) :
    (compactPairs54 K t).length ≤ K := by
  dsimp only [compactPairs54]
  split_ifs
  · simp only [List.length_map, List.length_zip, List.length_take, Finset.length_sort]
    have hcard : (Finset.univ.filter fun i : Fin K => t ⟨i.1, by omega⟩ = true).card ≤ K := by
      simpa using Finset.card_filter_le (Finset.univ : Finset (Fin K)) _
    omega
  · simp

lemma compactW54_size_le {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K)) :
    (compactW54 partEmb t).size ≤ K * s := by
  have hlen : ∀ ps : List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 },
      ((ps.map fun p => swapRegCircuit54 partEmb p.1.1 p.1.2 p.2).flatten).length = ps.length * s := by
    intro ps
    induction ps with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons]
      have hs : (swapRegCircuit54 partEmb p.1.1 p.1.2 p.2).length = s :=
        swapRegCircuit54_size partEmb p.1.1 p.1.2 p.2
      rw [hs]
      ring
  change (compactW54 partEmb t).length ≤ K * s
  rw [compactW54, hlen]
  exact Nat.mul_le_mul_right s (compactPairs54_length_le K t)

lemma compactW54_unitary {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K)) :
    Circuit.unitary (compactW54 partEmb t) =
      permMat (permutePart54 K s m partEmb (compactPerm54 K t)) := by
  have hgen : ∀ ps : List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 },
      Circuit.unitary ((ps.map fun p => swapRegCircuit54 partEmb p.1.1 p.1.2 p.2).flatten) =
        permMat (permutePart54 K s m partEmb (permOfPairs54 K ps)) := by
    intro ps
    induction ps with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, permOfPairs54, List.prod_nil]
      have h1 : permutePart54 K s m partEmb 1 = id := funext (permutePart54_one partEmb)
      rw [h1]
      ext y z
      simp [Circuit.unitary, permMat, Matrix.one_apply]
    | cons p rest ih =>
      rw [List.map_cons, List.flatten_cons, circuit_unitary_append, ih, swapRegCircuit54_unitary,
        permMat_mul_permMat]
      change permMat (permutePart54 K s m partEmb (permOfPairs54 K rest) ∘
          permutePart54 K s m partEmb (Equiv.swap p.1.1 p.1.2)) =
        permMat (permutePart54 K s m partEmb (Equiv.swap p.1.1 p.1.2 * permOfPairs54 K rest))
      congr 1
      funext z
      exact permutePart54_comp partEmb (Equiv.swap p.1.1 p.1.2) (permOfPairs54 K rest) z
  exact hgen (compactPairs54 K t)

lemma act_compactW54_ket {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K)) (z : Qubits m) :
    act (compactW54 partEmb t).unitary (ket z) =
      ket (permutePart54 K s m partEmb (compactPerm54 K t) z) := by
  rw [compactW54_unitary, act_permMat_ket]

private lemma permOfPairs54_disjoint_fixed {K : ℕ}
    (ps : List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })
    (j : Fin (2 * K))
    (hj1 : j ∉ ps.map (fun p => p.1.1))
    (hj2 : j ∉ ps.map (fun p => p.1.2)) :
    permOfPairs54 K ps j = j := by
  induction ps with
  | nil => simp [permOfPairs54]
  | cons p rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hj1 hj2
    change (Equiv.swap p.1.1 p.1.2 * permOfPairs54 K rest) j = j
    rw [Equiv.Perm.mul_apply, ih hj1.2 hj2.2,
      Equiv.swap_apply_of_ne_of_ne hj1.1 hj2.1]

private lemma permOfPairs54_disjoint_mem {K : ℕ}
    (ps : List { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })
    (hsplit : ∀ q ∈ ps, q.1.1.1 < K ∧ K ≤ q.1.2.1)
    (hnd1 : (ps.map (fun p => p.1.1)).Nodup)
    (hnd2 : (ps.map (fun p => p.1.2)).Nodup)
    {p : { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 }} (hp : p ∈ ps) :
    permOfPairs54 K ps p.1.1 = p.1.2 := by
  induction ps with
  | nil => exact absurd hp List.not_mem_nil
  | cons p₀ rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd1 hnd2
    have hsplit_rest : ∀ q ∈ rest, q.1.1.1 < K ∧ K ≤ q.1.2.1 :=
      fun q hq => hsplit q (List.mem_cons_of_mem p₀ hq)
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · have hp_lt : p.1.1.1 < K := (hsplit p List.mem_cons_self).1
      have hnot2 : p.1.1 ∉ rest.map (fun q => q.1.2) := by
        rw [List.mem_map]
        rintro ⟨q, hq, hqe⟩
        have := (hsplit_rest q hq).2
        have hv := congrArg Fin.val hqe
        omega
      change (Equiv.swap p.1.1 p.1.2 * permOfPairs54 K rest) p.1.1 = p.1.2
      rw [Equiv.Perm.mul_apply, permOfPairs54_disjoint_fixed rest p.1.1 hnd1.1 hnot2,
        Equiv.swap_apply_left]
    · have ih' := ih hsplit_rest hnd1.2 hnd2.2 hp_rest
      have hp_ge : K ≤ p.1.2.1 := (hsplit p (List.mem_cons_of_mem p₀ hp_rest)).2
      have hp₀_lt : p₀.1.1.1 < K := (hsplit p₀ List.mem_cons_self).1
      have hne1 : p.1.2 ≠ p₀.1.1 := by
        intro h; have hv := congrArg Fin.val h; omega
      have hne2 : p.1.2 ≠ p₀.1.2 := by
        intro h; apply hnd2.1; rw [List.mem_map]; exact ⟨p, hp_rest, h⟩
      change (Equiv.swap p₀.1.1 p₀.1.2 * permOfPairs54 K rest) p.1.1 = p.1.2
      rw [Equiv.Perm.mul_apply, ih']
      exact Equiv.swap_apply_of_ne_of_ne hne1 hne2

lemma compactPerm54_false {K : ℕ} {t : Qubits (2 * K)}
    (ht : K ≤ (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card)
    (k : Fin K) :
    t (compactPerm54 K t ⟨k.1, by omega⟩) = false := by
  let badL : Finset (Fin K) := Finset.univ.filter fun i : Fin K => t ⟨i.1, by omega⟩ = true
  let goodR : Finset (Fin K) := Finset.univ.filter fun i : Fin K => t ⟨K + i.1, by omega⟩ = false
  let goodL : Finset (Fin K) := Finset.univ.filter fun i : Fin K => t ⟨i.1, by omega⟩ = false
  have hpartL : goodL.card + badL.card = K := by
    have hdisj : Disjoint goodL badL := Finset.disjoint_filter.mpr fun i _ h1 h2 => by
      simp [h1] at h2
    have hunion : goodL ∪ badL = Finset.univ := by
      ext i
      simp only [goodL, badL, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases t ⟨i.1, by omega⟩ <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_fin]
  have hsplit_all : (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card =
      goodL.card + goodR.card := by
    let e : Fin (2 * K) ≃ Fin K ⊕ Fin K :=
      { toFun := fun j => if h : j.1 < K then Sum.inl ⟨j.1, h⟩ else Sum.inr ⟨j.1 - K, by omega⟩
        invFun := fun s => match s with | Sum.inl i => ⟨i.1, by omega⟩ | Sum.inr i => ⟨K + i.1, by omega⟩
        left_inv := fun j => by
          by_cases h : j.1 < K
          · simp [h]
          · simp [h]; ext; simp; omega
        right_inv := fun s => by
          rcases s with i | i
          · simp [i.isLt]
          · have hnot : ¬ (K + i.1 < K) := by omega
            simp [hnot] }
    let F_sum : Finset (Fin K ⊕ Fin K) :=
      Finset.univ.filter fun s => t (e.symm s) = false
    have hcard_e : (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card = F_sum.card := by
      refine Finset.card_bij (fun j _ => e j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [F_sum, hj]
      · intro j₁ _ j₂ _ h; exact e.injective h
      · intro s hs
        simp only [F_sum, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact ⟨e.symm s, by simp [hs], e.apply_symm_apply s⟩
    have hcard_sum : F_sum.card = goodL.card + goodR.card := by
      let F_L := F_sum.filter fun s => Sum.isLeft s = true
      let F_R := F_sum.filter fun s => Sum.isRight s = true
      have hdisj : Disjoint F_L F_R := Finset.disjoint_filter.mpr fun s _ h1 h2 => by
        cases s <;> simp_all
      have hunion : F_L ∪ F_R = F_sum := by
        ext s; cases s <;> simp [F_L, F_R]
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
      have hL : F_L.card = goodL.card := by
        refine Finset.card_bij (fun s hs => match s with | Sum.inl i => i | Sum.inr i => i) ?_ ?_ ?_
        · intro s hs
          rcases s with i | i
          · simp only [F_L, F_sum, Finset.mem_filter, Finset.mem_univ, true_and, Sum.isLeft_inl,
              and_true] at hs
            simpa [goodL, e] using hs
          · simp [F_L] at hs
        · intro s₁ hs₁ s₂ hs₂ h
          rcases s₁ with i₁ | i₁ <;> rcases s₂ with i₂ | i₂
          · simp at h; rw [h]
          · simp [F_L] at hs₂
          · simp [F_L] at hs₁
          · simp [F_L] at hs₁
        · intro i hi
          simp only [goodL, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨Sum.inl i, ?_, rfl⟩
          simp [F_L, F_sum, e, hi]
      have hR : F_R.card = goodR.card := by
        refine Finset.card_bij (fun s hs => match s with | Sum.inl i => i | Sum.inr i => i) ?_ ?_ ?_
        · intro s hs
          rcases s with i | i
          · simp [F_R] at hs
          · simp only [F_R, F_sum, Finset.mem_filter, Finset.mem_univ, true_and, Sum.isRight_inr,
              and_true] at hs
            simpa [goodR, e] using hs
        · intro s₁ hs₁ s₂ hs₂ h
          rcases s₁ with i₁ | i₁ <;> rcases s₂ with i₂ | i₂
          · simp [F_R] at hs₁
          · simp [F_R] at hs₁
          · simp [F_R] at hs₂
          · simp at h; rw [h]
        · intro i hi
          simp only [goodR, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨Sum.inr i, ?_, rfl⟩
          simp [F_R, F_sum, e, hi]
      rw [hL, hR]
    rw [hcard_e, hcard_sum]
  have hbad_le_good : badL.card ≤ goodR.card := by omega
  let bs : List (Fin K) := badL.sort (· ≤ ·)
  let gs : List (Fin K) := (goodR.sort (· ≤ ·)).take badL.card
  let ps := compactPairs54 K t
  have hps_eq : ps = (bs.zip gs).map fun p =>
      ⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), by
        intro h; have hv := congrArg Fin.val h; dsimp at hv; omega⟩ := by
    simp [ps, compactPairs54, ht, bs, gs, badL, goodR]
  by_cases htk : t ⟨k.1, by omega⟩ = false
  · have hk_not1 : (⟨k.1, by omega⟩ : Fin (2 * K)) ∉ ps.map (fun p => p.1.1) := by
      rw [hps_eq, List.mem_map]
      rintro ⟨p, hp_mem, hp_eq⟩
      rw [List.mem_map] at hp_mem
      rcases hp_mem with ⟨⟨i, j⟩, hij, rfl⟩
      have hi_mem : i ∈ bs := (List.of_mem_zip hij).1
      have hi_bad : i ∈ badL := (Finset.mem_sort (· ≤ ·)).mp hi_mem
      simp only [badL, Finset.mem_filter, Finset.mem_univ, true_and] at hi_bad
      have hki : k = i := Fin.ext (congrArg Fin.val hp_eq).symm
      rw [← hki] at hi_bad
      rw [htk] at hi_bad
      cases hi_bad
    have hk_not2 : (⟨k.1, by omega⟩ : Fin (2 * K)) ∉ ps.map (fun p => p.1.2) := by
      rw [hps_eq, List.mem_map]
      rintro ⟨p, hp_mem, hp_eq⟩
      rw [List.mem_map] at hp_mem
      rcases hp_mem with ⟨⟨i, j⟩, _, rfl⟩
      have hv := congrArg Fin.val hp_eq
      dsimp at hv
      omega
    change t (permOfPairs54 K ps ⟨k.1, by omega⟩) = false
    rw [permOfPairs54_disjoint_fixed ps ⟨k.1, by omega⟩ hk_not1 hk_not2]
    exact htk
  · have htk_true : t ⟨k.1, by omega⟩ = true := by
      cases h : t ⟨k.1, by omega⟩ <;> simp_all
    have hk_bad : k ∈ badL := by
      simp [badL, htk_true]
    have hk_bs : k ∈ bs := (Finset.mem_sort (· ≤ ·)).mpr hk_bad
    have hlen_gs : gs.length = badL.card := by
      simp [gs, List.length_take, Finset.length_sort, hbad_le_good]
    have hlen_bs : bs.length = badL.card := Finset.length_sort (· ≤ ·)
    have hfst : (bs.zip gs).map Prod.fst = bs := by
      rw [List.map_fst_zip (by omega)]
    have hk_zip : k ∈ (bs.zip gs).map Prod.fst := hfst.symm ▸ hk_bs
    rw [List.mem_map] at hk_zip
    rcases hk_zip with ⟨⟨i, j⟩, hij, hki⟩
    dsimp only at hki
    subst hki
    have hj_gs : j ∈ gs := (List.of_mem_zip hij).2
    have hj_sort : j ∈ goodR.sort (· ≤ ·) := List.mem_of_mem_take hj_gs
    have hj_good : j ∈ goodR := (Finset.mem_sort (· ≤ ·)).mp hj_sort
    simp only [goodR, Finset.mem_filter, Finset.mem_univ, true_and] at hj_good
    let p : { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 } :=
      ⟨(⟨i.1, by omega⟩, ⟨K + j.1, by omega⟩), by
        intro h; have hv := congrArg Fin.val h; dsimp at hv; omega⟩
    have hp_mem : p ∈ ps := by
      rw [hps_eq, List.mem_map]
      exact ⟨(i, j), hij, rfl⟩
    have hsplit : ∀ q ∈ ps, q.1.1.1 < K ∧ K ≤ q.1.2.1 := by
      intro q hq
      rw [hps_eq, List.mem_map] at hq
      rcases hq with ⟨⟨a, b⟩, _, rfl⟩
      exact ⟨a.isLt, Nat.le_add_right K b.1⟩
    have hnd1 : (ps.map (fun p => p.1.1)).Nodup := by
      rw [hps_eq, List.map_map]
      have hmap : (List.map ((fun p => p.1.1) ∘ fun p : Fin K × Fin K =>
          (⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), fun h => by
            have hv := congrArg Fin.val h; dsimp at hv; omega⟩ :
            { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })) (bs.zip gs)) =
          bs.map (fun a : Fin K => (⟨a.1, by omega⟩ : Fin (2 * K))) := by
        calc List.map ((fun p => p.1.1) ∘ fun p : Fin K × Fin K =>
              (⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), fun h => by
                have hv := congrArg Fin.val h; dsimp at hv; omega⟩ :
                { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })) (bs.zip gs)
            = List.map (fun a : Fin K => (⟨a.1, by omega⟩ : Fin (2 * K)))
                ((bs.zip gs).map Prod.fst) := by
                simp [List.map_map, Function.comp_def]
          _ = bs.map (fun a : Fin K => (⟨a.1, by omega⟩ : Fin (2 * K))) := by rw [hfst]
      rw [hmap]
      exact (badL.sort_nodup (· ≤ ·)).map fun a₁ a₂ h =>
        Fin.ext (by simpa using congrArg Fin.val h)
    have hnd2 : (ps.map (fun p => p.1.2)).Nodup := by
      rw [hps_eq, List.map_map]
      have hsnd : (bs.zip gs).map Prod.snd = gs := by
        rw [List.map_snd_zip (by omega)]
      have hmap : (List.map ((fun p => p.1.2) ∘ fun p : Fin K × Fin K =>
          (⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), fun h => by
            have hv := congrArg Fin.val h; dsimp at hv; omega⟩ :
            { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })) (bs.zip gs)) =
          gs.map (fun b : Fin K => (⟨K + b.1, by omega⟩ : Fin (2 * K))) := by
        calc List.map ((fun p => p.1.2) ∘ fun p : Fin K × Fin K =>
              (⟨(⟨p.1.1, by omega⟩, ⟨K + p.2.1, by omega⟩), fun h => by
                have hv := congrArg Fin.val h; dsimp at hv; omega⟩ :
                { p : Fin (2 * K) × Fin (2 * K) // p.1 ≠ p.2 })) (bs.zip gs)
            = List.map (fun b : Fin K => (⟨K + b.1, by omega⟩ : Fin (2 * K)))
                ((bs.zip gs).map Prod.snd) := by
                simp [List.map_map, Function.comp_def]
          _ = gs.map (fun b : Fin K => (⟨K + b.1, by omega⟩ : Fin (2 * K))) := by rw [hsnd]
      rw [hmap]
      have hgs_nd : gs.Nodup := (goodR.sort_nodup (· ≤ ·)).take
      exact hgs_nd.map fun b₁ b₂ h => Fin.ext (by
        have hv := congrArg Fin.val h; dsimp at hv; omega)
    change t (permOfPairs54 K ps p.1.1) = false
    rw [permOfPairs54_disjoint_mem ps hsplit hnd1 hnd2 hp_mem]
    exact hj_good

/-! ### 3. Asymptotic Gate-Count Bounds (`n ≥ 1`) -/

lemma real_log_four_gt_one : (1 : ℝ) < Real.log 4 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

lemma clog2_add_one_bound {X : ℕ} (hX : 3 ≤ X) :
    ((Nat.clog 2 (X + 2) + 1 : ℕ) : ℝ) ≤ (4 / Real.log 2) * Real.log X := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let c := Nat.clog 2 (X + 2)
  have hc1 : 1 ≤ c := by
    dsimp [c]
    by_contra hc0
    have hcz : c = 0 := by omega
    have hle := Nat.le_pow_clog (b := 2) (by norm_num) (X + 2)
    change X + 2 ≤ 2 ^ c at hle
    rw [hcz, pow_zero] at hle
    omega
  have hpred_lt : c - 1 < c := by omega
  have hpow_lt : 2 ^ (c - 1) < X + 2 := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
  have hpow_le : (2 : ℝ) ^ (c - 1) ≤ 2 * (X : ℝ) := by
    norm_cast
    omega
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (c - 1) := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hlog_pow : ((c - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log X := by
    have h1 := Real.log_le_log hpow_pos hpow_le
    have h2 : Real.log ((2 : ℝ) ^ (c - 1)) = ((c - 1 : ℕ) : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    have h3 : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log X :=
      Real.log_mul (by norm_num) hXpos.ne'
    linarith
  have hc_le : ((c - 1 : ℕ) : ℝ) ≤ 1 + Real.log X / Real.log 2 := by
    have hdiv := (le_div_iff₀ hlog2_pos).mpr hlog_pow
    calc ((c - 1 : ℕ) : ℝ) ≤ (Real.log 2 + Real.log X) / Real.log 2 := hdiv
      _ = 1 + Real.log X / Real.log 2 := by field_simp
  have hlogX_ge : Real.log 2 ≤ Real.log X := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (by omega : 2 ≤ X)
  have h1_le : (1 : ℝ) ≤ Real.log X / Real.log 2 := (one_le_div hlog2_pos).mpr hlogX_ge
  have heq : ((Nat.clog 2 (X + 2) + 1 : ℕ) : ℝ) = ((c - 1 : ℕ) : ℝ) + 2 := by
    have hnat : Nat.clog 2 (X + 2) + 1 = (c - 1) + 2 := by dsimp [c]; omega
    rw [hnat]
    push_cast
    rfl
  rw [heq]
  calc ((c - 1 : ℕ) : ℝ) + 2 ≤ 3 + Real.log X / Real.log 2 := by linarith
    _ ≤ 3 * (Real.log X / Real.log 2) + Real.log X / Real.log 2 := by linarith
    _ = (4 / Real.log 2) * Real.log X := by ring

lemma s_bound_n_pos {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.clog 2 n + 1 : ℕ) : ℝ) ≤ (3 / Real.log 2) * Real.log (n + 1) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn1_ge : Real.log 2 ≤ Real.log (n + 1) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (by omega : 2 ≤ n + 1)
  have h1_le : (1 : ℝ) ≤ Real.log (n + 1) / Real.log 2 := (one_le_div hlog2_pos).mpr hlogn1_ge
  by_cases hn1 : n = 1
  · subst hn1
    simp only [Nat.clog_one_right, zero_add, Nat.cast_one]
    have h2 : ((1 : ℝ) + 1) = 2 := by norm_num
    rw [h2]
    field_simp
    norm_num
  · have hn2 : 2 ≤ n := by omega
    let c := Nat.clog 2 n
    have hc1 : 1 ≤ c := by
      dsimp [c]
      by_contra hc0
      have hcz : c = 0 := by omega
      have hle := Nat.le_pow_clog (b := 2) (by norm_num) n
      change n ≤ 2 ^ c at hle
      rw [hcz, pow_zero] at hle
      omega
    have hpred_lt : c - 1 < c := by omega
    have hpow_lt : 2 ^ (c - 1) < n := (Nat.lt_clog_iff_pow_lt (by norm_num)).mp hpred_lt
    have hpow_le : (2 : ℝ) ^ (c - 1) ≤ (n + 1 : ℝ) := by
      exact_mod_cast (by omega : 2 ^ (c - 1) ≤ n + 1)
    have hlog_pow : ((c - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (n + 1) := by
      have h1 := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (c - 1)) hpow_le
      rwa [Real.log_pow] at h1
    have hc_le : ((c - 1 : ℕ) : ℝ) ≤ Real.log (n + 1) / Real.log 2 :=
      (le_div_iff₀ hlog2_pos).mpr hlog_pow
    have heq : ((Nat.clog 2 n + 1 : ℕ) : ℝ) = ((c - 1 : ℕ) : ℝ) + 2 := by
      have hnat : Nat.clog 2 n + 1 = (c - 1) + 2 := by dsimp [c]; omega
      rw [hnat]; push_cast; rfl
    rw [heq]
    calc ((c - 1 : ℕ) : ℝ) + 2 ≤ Real.log (n + 1) / Real.log 2 + 2 := by linarith
      _ ≤ Real.log (n + 1) / Real.log 2 + 2 * (Real.log (n + 1) / Real.log 2) := by linarith
      _ = (3 / Real.log 2) * Real.log (n + 1) := by ring

lemma asymptotic_gate_bound_54 (C_V : ℝ) (hCV : 0 < C_V) (K_V : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n K D q : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        let s := Nat.clog 2 n + 1
        (2 * K : ℝ) ≤ C * K ∧
        C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) +
          C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) * ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V +
          3 * (K : ℝ) * (s : ℝ) ≤
          C * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) +
            C * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  let C₁ : ℝ := 4 * C_V / Real.log 2
  let C₂ : ℝ := C_V * (3 / Real.log 2) * (4 / Real.log 2) ^ K_V + 9 / Real.log 2
  let C : ℝ := max 2 (max C₁ C₂)
  refine ⟨C, by dsimp [C]; positivity, fun n K D q hn hK hD hq => ?_⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · have h2C : (2 : ℝ) ≤ C := le_max_left _ _
    exact mul_le_mul_of_nonneg_right h2C (Nat.cast_nonneg K)
  · let s := Nat.clog 2 n + 1
    change C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) +
        C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) * ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V +
        3 * (K : ℝ) * (s : ℝ) ≤
      C * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) +
        C * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V
    have hD3 : 3 ≤ D := by omega
    have hnD3 : 3 ≤ n * D := by nlinarith
    have hlog2q_eq : Real.log ((2 : ℝ) ^ q) = (q : ℝ) * Real.log 2 := Real.log_pow 2 q
    have hq_le : (q : ℝ) ≤ (1 / Real.log 2) * Real.log (2 ^ q) := by
      rw [hlog2q_eq]; field_simp; rfl
    have hc_nD : ((Nat.clog 2 (n * D + 2) + 1 : ℕ) : ℝ) ≤ (4 / Real.log 2) * Real.log (n * D) := by
      simpa [Nat.cast_mul] using clog2_add_one_bound hnD3
    have hlog2q_nn : 0 ≤ Real.log (2 ^ q) := Real.log_nonneg (by
      exact_mod_cast (by have := Nat.one_le_two_pow (n := q); omega : 1 ≤ 2 ^ q))
    have hlognD_nn : 0 ≤ Real.log (n * D) := Real.log_nonneg (by
      exact_mod_cast (by omega : 1 ≤ n * D))
    have hterm1 : C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) ≤
        C₁ * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) := by
      have hsum : (q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ) ≤
          (4 / Real.log 2) * (Real.log (2 ^ q) + Real.log (n * D)) := by
        have hq4 : (1 / Real.log 2) * Real.log (2 ^ q) ≤ (4 / Real.log 2) * Real.log (2 ^ q) := by
          have : 1 / Real.log 2 ≤ 4 / Real.log 2 := div_le_div_of_nonneg_right (by norm_num) hlog2_pos.le
          exact mul_le_mul_of_nonneg_right this hlog2q_nn
        linarith
      have hmul := mul_le_mul_of_nonneg_left hsum (mul_nonneg hCV.le (Nat.cast_nonneg n))
      calc C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ))
          ≤ C_V * (n : ℝ) * ((4 / Real.log 2) * (Real.log (2 ^ q) + Real.log (n * D))) := hmul
        _ = C₁ * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) := by dsimp [C₁]; ring
    have hs_le : (s : ℝ) ≤ (3 / Real.log 2) * Real.log (n + 1) := s_bound_n_pos hn
    have h3_div_ge1 : (1 : ℝ) ≤ 3 / Real.log 2 := by
      rw [one_le_div hlog2_pos]; linarith
    have hKn : (n : ℝ) + (K : ℝ) * (s : ℝ) ≤ (3 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) := by
      have hn_le : (n : ℝ) ≤ (3 / Real.log 2) * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_right h3_div_ge1 (Nat.cast_nonneg n)
        linarith
      have hKs_le : (K : ℝ) * (s : ℝ) ≤ (3 / Real.log 2) * ((K : ℝ) * Real.log (n + 1)) := by
        have := mul_le_mul_of_nonneg_left hs_le (Nat.cast_nonneg K)
        linarith
      linarith
    have hKn4 : 4 ≤ (K + 1) * (n + 1) := by nlinarith
    have hlogKn_gt1 : (1 : ℝ) < Real.log ((K + 1) * (n + 1)) := by
      have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by exact_mod_cast hKn4 : (4 : ℝ) ≤ (K + 1) * (n + 1))
      exact lt_of_lt_of_le real_log_four_gt_one (by simpa [Nat.cast_mul, Nat.cast_add] using hle)
    have hclog_Kn : ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ≤
        (4 / Real.log 2) * Real.log ((K + 1) * (n + 1)) := by
      simpa [Nat.cast_mul, Nat.cast_add] using clog2_add_one_bound (by omega : 3 ≤ (K + 1) * (n + 1))
    have hclog_pow : ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V ≤
        (4 / Real.log 2) ^ K_V * Real.log ((K + 1) * (n + 1)) ^ K_V := by
      have h1 := pow_le_pow_left₀ (by positivity) hclog_Kn K_V
      rwa [mul_pow] at h1
    have hlog_n1_nn : 0 ≤ Real.log (n + 1) := Real.log_nonneg (by
      exact_mod_cast (by omega : 1 ≤ n + 1))
    have hbase_nn : 0 ≤ (n : ℝ) + (K : ℝ) * Real.log (n + 1) := by positivity
    have hlogpow_ge1 : (1 : ℝ) ≤ Real.log ((K + 1) * (n + 1)) ^ K_V :=
      one_le_pow₀ hlogKn_gt1.le
    have hterm2 : C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V ≤
        C_V * (3 / Real.log 2) * (4 / Real.log 2) ^ K_V *
          ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by
      have h1 : ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V ≤
          ((3 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1))) *
            ((4 / Real.log 2) ^ K_V * Real.log ((K + 1) * (n + 1)) ^ K_V) :=
        mul_le_mul hKn hclog_pow (by positivity) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 hCV.le
      calc C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V
          = C_V * (((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V) := by ring
        _ ≤ C_V * (((3 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1))) *
            ((4 / Real.log 2) ^ K_V * Real.log ((K + 1) * (n + 1)) ^ K_V)) := h2
        _ = C_V * (3 / Real.log 2) * (4 / Real.log 2) ^ K_V *
            ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by ring
    have hterm3 : 3 * (K : ℝ) * (s : ℝ) ≤
        (9 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by
      have h1 : 3 * (K : ℝ) * (s : ℝ) ≤ (9 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) := by
        have hKs := mul_le_mul_of_nonneg_left hs_le (by positivity : 0 ≤ 3 * (K : ℝ))
        have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        calc 3 * (K : ℝ) * (s : ℝ) ≤ 3 * (K : ℝ) * ((3 / Real.log 2) * Real.log (n + 1)) := hKs
          _ = (9 / Real.log 2) * ((K : ℝ) * Real.log (n + 1)) := by ring
          _ ≤ (9 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) := by
              apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left hlogpow_ge1 (by positivity : 0 ≤ (9 / Real.log 2) * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)))
      linarith
    have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have hC2 : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have hsum1 : C₁ * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) ≤
        C * (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) := by
      have hnn : 0 ≤ (n : ℝ) * (Real.log (2 ^ q) + Real.log (n * D)) := mul_nonneg (Nat.cast_nonneg n) (add_nonneg hlog2q_nn hlognD_nn)
      have h := mul_le_mul_of_nonneg_right hC1 hnn
      linarith
    have hsum2 : C₂ * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V ≤
        C * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by
      have hnn : 0 ≤ ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V :=
        mul_nonneg hbase_nn (by positivity)
      have h := mul_le_mul_of_nonneg_right hC2 hnn
      linarith
    have h23 : C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V + 3 * (K : ℝ) * (s : ℝ) ≤
        C₂ * ((n : ℝ) + (K : ℝ) * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K_V := by
      dsimp [C₂]; linarith
    linarith

lemma outEmb54_finProd_splitReg {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (π : Equiv.Perm (Fin (2 * K))) (z : Qubits m) (k : Fin K) :
    splitReg K s (permutePart54 K s m partEmb π z ∘ outEmb54 K s m partEmb) k =
      splitReg (2 * K) s (z ∘ partEmb) (π ⟨k.1, by omega⟩) := by
  funext c
  change permutePart54 K s m partEmb π z (outEmb54 K s m partEmb (finProdFinEquiv (k, c))) =
    z (partWire54 partEmb (π ⟨k.1, by omega⟩) c)
  rw [outEmb54_finProd, permutePart54_in]

def measEmb54 {K s m : ℕ} (hs : 1 ≤ s) (partEmb : Fin (2 * K * s) ↪ Fin m) :
    Fin (2 * K) ↪ Fin m where
  toFun j := partWire54 partEmb j ⟨0, hs⟩
  inj' _ _ h := (partWire54_inj partEmb h).1

lemma compactW54_summary {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K)) :
    (compactW54 partEmb t).size ≤ K * s ∧
    ((compactW54 partEmb t).size : ℝ) ≤ 3 * K * s ∧
    (∀ z : Qubits m, act (compactW54 partEmb t).unitary (ket z) =
      ket (permutePart54 K s m partEmb (compactPerm54 K t) z)) ∧
    (K ≤ (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card →
      ∀ k : Fin K, t (compactPerm54 K t ⟨k.1, by omega⟩) = false) := by
  refine ⟨compactW54_size_le partEmb t, ?_, act_compactW54_ket partEmb t, fun ht k =>
    compactPerm54_false ht k⟩
  have hle : ((compactW54 partEmb t).size : ℝ) ≤ (K * s : ℕ) :=
    Nat.cast_le.mpr (compactW54_size_le partEmb t)
  push_cast at hle
  have hnn : 0 ≤ (K : ℝ) * (s : ℝ) := by positivity
  linarith

lemma permutePart54_eq_permPartReg54 {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (σ : Equiv.Perm (Fin (2 * K))) (x : Qubits m) :
    permutePart54 K s m partEmb σ x = permPartReg54 partEmb σ x := by
  funext a
  by_cases ha : a ∈ Set.range partEmb
  · obtain ⟨q, rfl⟩ := ha
    obtain ⟨⟨j, c⟩, hq⟩ := finProdFinEquiv.surjective q
    rw [← hq]
    change permutePart54 K s m partEmb σ x (partWire54 partEmb j c) =
      permPartReg54 partEmb σ x (partEmb (finProdFinEquiv (j, c)))
    rw [permutePart54_in, permPartReg54_part]
    rfl
  · rw [permutePart54_out _ _ _ ha, permPartReg54_off _ _ _ ha]

lemma compactW54_for_band_channel {K s m : ℕ} (partEmb : Fin (2 * K * s) ↪ Fin m)
    (t : Qubits (2 * K))
    (ht : K ≤ (Finset.univ.filter fun j : Fin (2 * K) => t j = false).card) :
    ∃ σ : Equiv.Perm (Fin (2 * K)),
      (∀ k : Fin K, t (σ ⟨k.val, by omega⟩) = false) ∧
      ∀ x : Qubits m, act (compactW54 partEmb t).unitary (ket x) =
        ket (permPartReg54 partEmb σ x) :=
  ⟨compactPerm54 K t, fun k => compactPerm54_false ht k, fun x => by
    rw [act_compactW54_ket, permutePart54_eq_permPartReg54]⟩

lemma theorem_5_4_from_sym_witness
    (C_V : ℝ) (hCV : 0 < C_V) (K_V : ℕ)
    (hsym : ∀ (n K D q : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      let s := Nat.clog 2 n + 1
      ∃ (e : ℕ) (V : Circuit gates12 (n * q + e))
        (partEmb : Fin (2 * K * s) ↪ Fin (n * q + e))
        (degState : ℕ → Qubits (n * q + e)),
        (V.size : ℝ) ≤ C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) +
          C_V * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V ∧
        ∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K),
          act V.unitary (padKet e (ket (flatReg n q fun i => natToBits q (α i)))) =
            embedPartAndDeg54 partEmb (multinomKet54 n s K α hk) (degState (∑ i, α i))) :
    ∃ C : ℝ, 0 < C ∧ ∃ K' : ℕ,
      ∀ (n K D q : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        ∃ (s e r : ℕ) (V : Circuit gates12 (n * q + e)) (W : Qubits r → Circuit gates12 (n * q + e))
          (meas : Fin r ↪ Fin (n * q + e)) (out : Fin (K * s) ↪ Fin (n * q + e)),
          n ≤ 2 ^ s ∧ (r : ℝ) ≤ C * K ∧
          (∀ t : Qubits r, ((V.size + (W t).size : ℕ) : ℝ) ≤
            C * n * (Real.log (2 ^ q) + Real.log (n * D)) +
              C * (n + K * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K') ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            measChannelOut V.unitary (fun t => (W t).unitary) meas out
              (padKet e (bandKet n q K w)) = dirTensorPow s K w := by
  obtain ⟨C, hC, hbd⟩ := asymptotic_gate_bound_54 C_V hCV K_V
  refine ⟨C, hC, K_V, fun n K D q hK hD hq => ?_⟩
  by_cases hn0 : n = 0
  · subst hn0
    simpa using theorem_5_4_n_zero hC K_V hK hD hq
  · have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
    let s : ℕ := Nat.clog 2 n + 1
    obtain ⟨e, V, partEmb, degState, hVsize, hVact⟩ := hsym n K D q hn hK hD hq
    obtain ⟨hr_le, hgate_le⟩ := hbd n K D q hn hK hD hq
    let meas : Fin (2 * K) ↪ Fin (n * q + e) := measEmb54 (Nat.succ_pos _) partEmb
    let out : Fin (K * s) ↪ Fin (n * q + e) := outEmb54 K s (n * q + e) partEmb
    let W : Qubits (2 * K) → Circuit gates12 (n * q + e) := fun t => compactW54 partEmb t
    have hns : n ≤ 2 ^ s := le_trans (Nat.le_pow_clog (by norm_num) n)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ _))
    refine ⟨s, e, 2 * K, V, W, meas, out, hns, ?_, ?_, ?_⟩
    · simpa [Nat.cast_mul, Nat.cast_ofNat] using hr_le
    · intro t
      have hW_size : ((W t).size : ℝ) ≤ 3 * (K : ℝ) * (s : ℝ) :=
        (compactW54_summary partEmb t).2.1
      have hsum : ((V.size + (W t).size : ℕ) : ℝ) = (V.size : ℝ) + ((W t).size : ℝ) := by
        push_cast; rfl
      rw [hsum]
      exact le_trans (add_le_add hVsize hW_size) hgate_le
    · intro w hw
      exact band_channel_algebra_54 n K D q e hn hK hD hq partEmb meas out V.unitary
        (fun t => (W t).unitary) degState (fun _ => rfl) (outEmb54_finProd partEmb)
        hVact (fun t ht => compactW54_for_band_channel partEmb t ht) w hw

/-! ### 5. Stage A (`occupation_to_nsil_54`) + Stage B (`nsil_symmetrize_54`) Composition Glue -/

def embedCircuit54 {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    Circuit S m :=
  c.map fun g => ⟨g.gate, g.mem, g.wires.trans emb⟩

lemma embedCircuit54_size {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    (embedCircuit54 emb c).size = c.size :=
  List.length_map _

lemma embedCircuit54_unitary {S : Set Gate} {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (c : Circuit S m₀) :
    (embedCircuit54 emb c).unitary = embedOp c.unitary emb := by
  unfold Circuit.unitary embedCircuit54
  induction c with
  | nil => simp [embedOp_one]
  | cons g gs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one] at ih ⊢
    rw [ih, embedOp_mul, embedOp_embedOp]

private noncomputable def updateOn54 {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (d : Qubits m) :
    Qubits m₀ ↪ Qubits m where
  toFun x a := open Classical in if h : ∃ i, emb i = a then x (Classical.choose h) else d a
  inj' x₁ x₂ h := by
    classical
    funext i
    have hi := congrFun h (emb i)
    have hex : ∃ j, emb j = emb i := ⟨i, rfl⟩
    change (if h' : ∃ j, emb j = emb i then x₁ (Classical.choose h') else d (emb i)) =
      (if h' : ∃ j, emb j = emb i then x₂ (Classical.choose h') else d (emb i)) at hi
    rw [dif_pos hex, dif_pos hex, emb.injective (Classical.choose_spec hex)] at hi
    exact hi

private lemma updateOn54_comp {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (d : Qubits m)
    (x : Qubits m₀) : updateOn54 emb d x ∘ emb = x := by
  classical
  funext i
  have hex : ∃ j, emb j = emb i := ⟨i, rfl⟩
  change (if h' : ∃ j, emb j = emb i then x (Classical.choose h') else d (emb i)) = x i
  rw [dif_pos hex, emb.injective (Classical.choose_spec hex)]

private lemma updateOn54_off {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) (d : Qubits m)
    (x : Qubits m₀) {a : Fin m} (ha : a ∉ Set.range emb) :
    updateOn54 emb d x a = d a := by
  classical
  have hnot : ¬ ∃ i, emb i = a := ha
  change (if h' : ∃ i, emb i = a then x (Classical.choose h') else d a) = d a
  rw [dif_neg hnot]

private lemma eq_updateOn54_of_agree {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m) {d u : Qubits m}
    (hu : ∀ a : Fin m, a ∉ Set.range emb → u a = d a) :
    u = updateOn54 emb d (u ∘ emb) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range emb
  · obtain ⟨i, rfl⟩ := ha
    exact (congrFun (updateOn54_comp emb d (u ∘ emb)) i).symm
  · rw [updateOn54_off emb d _ ha, hu a ha]

lemma act_embedOp_embedPartAndDeg54 {m₀ m : ℕ} (emb : Fin m₀ ↪ Fin m)
    (U : Matrix (Qubits m₀) (Qubits m₀) ℂ) (ψ : EuclideanSpace ℂ (Qubits m₀)) (d : Qubits m) :
    act (embedOp U emb) (embedPartAndDeg54 emb ψ d) = embedPartAndDeg54 emb (act U ψ) d := by
  classical
  ext z
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    embedPartAndDeg54_apply]
  by_cases hz : ∀ a : Fin m, a ∉ Set.range emb → z a = d a
  · rw [if_pos hz]
    have hsub : (∑ u : Qubits m,
          (if ∀ a, a ∉ Set.range emb → z a = u a then U (z ∘ emb) (u ∘ emb) else 0) *
          (if ∀ a, a ∉ Set.range emb → u a = d a then ψ (fun i => u (emb i)) else 0)) =
        ∑ u ∈ Finset.univ.image (updateOn54 emb d),
          (if ∀ a, a ∉ Set.range emb → z a = u a then U (z ∘ emb) (u ∘ emb) else 0) *
          (if ∀ a, a ∉ Set.range emb → u a = d a then ψ (fun i => u (emb i)) else 0) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro u _ hu
      by_cases hud : ∀ a, a ∉ Set.range emb → u a = d a
      · exfalso; apply hu; rw [Finset.mem_image]
        exact ⟨u ∘ emb, Finset.mem_univ _, (eq_updateOn54_of_agree emb hud).symm⟩
      · rw [if_neg hud, mul_zero]
    change (∑ u : Qubits m,
          (if ∀ a, a ∉ Set.range emb → z a = u a then U (z ∘ emb) (u ∘ emb) else 0) *
          (if ∀ a, a ∉ Set.range emb → u a = d a then ψ (fun i => u (emb i)) else 0)) = _
    rw [hsub, Finset.sum_image (fun x₁ _ x₂ _ h => (updateOn54 emb d).injective h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ∀ a, a ∉ Set.range emb → z a = updateOn54 emb d x a := fun a ha => by
      rw [hz a ha, updateOn54_off emb d x ha]
    have h2 : ∀ a, a ∉ Set.range emb → updateOn54 emb d x a = d a := fun a ha =>
      updateOn54_off emb d x ha
    rw [if_pos h1, if_pos h2]
    have hcomp : (fun i => updateOn54 emb d x (emb i)) = x := updateOn54_comp emb d x
    rw [hcomp, updateOn54_comp]
    rfl
  · rw [if_neg hz]
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : ∀ a, a ∉ Set.range emb → z a = u a
    · have h2 : ¬ ∀ a, a ∉ Set.range emb → u a = d a := fun h2 =>
        hz fun a ha => (h1 a ha).trans (h2 a ha)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

def occEmb54 (nq e_occ e_sym : ℕ) : Fin (nq + e_occ) ↪ Fin (nq + (e_occ + e_sym)) where
  toFun i := ⟨i.1, by omega⟩
  inj' _ _ h := Fin.ext (by simpa using congrArg Fin.val h)

@[simp] lemma occEmb54_apply (nq e_occ e_sym : ℕ) (i : Fin (nq + e_occ)) :
    (occEmb54 nq e_occ e_sym i).1 = i.1 := rfl

def ancSymEmb54 (nq e_occ e_sym : ℕ) : Fin e_sym ↪ Fin (nq + (e_occ + e_sym)) where
  toFun j := ⟨nq + e_occ + j.1, by omega⟩
  inj' _ _ h := Fin.ext (by have hv := congrArg Fin.val h; dsimp at hv; omega)

@[simp] lemma ancSymEmb54_apply (nq e_occ e_sym : ℕ) (j : Fin e_sym) :
    (ancSymEmb54 nq e_occ e_sym j).1 = nq + e_occ + j.1 := rfl

def symEmb54 {nq e_occ e_sym K s : ℕ}
    (partEmb_occ : Fin (2 * K * s) ↪ Fin (nq + e_occ)) :
    Fin (2 * K * s + e_sym) ↪ Fin (nq + (e_occ + e_sym)) where
  toFun := Fin.addCases (partEmb_occ.trans (occEmb54 nq e_occ e_sym)) (ancSymEmb54 nq e_occ e_sym)
  inj' := by
    intro x y h
    induction x using Fin.addCases <;> induction y using Fin.addCases
    · simp only [Fin.addCases_left] at h
      rw [(partEmb_occ.trans (occEmb54 nq e_occ e_sym)).injective h]
    · simp only [Fin.addCases_left, Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      rename_i i₁ j₂
      have hlt := (partEmb_occ i₁).isLt
      change (partEmb_occ i₁).1 = nq + e_occ + j₂.1 at hv
      omega
    · simp only [Fin.addCases_right, Fin.addCases_left] at h
      have hv := congrArg Fin.val h
      rename_i j₁ i₂
      have hlt := (partEmb_occ i₂).isLt
      change nq + e_occ + j₁.1 = (partEmb_occ i₂).1 at hv
      omega
    · simp only [Fin.addCases_right] at h
      rw [(ancSymEmb54 nq e_occ e_sym).injective h]

@[simp] lemma symEmb54_castAdd {nq e_occ e_sym K s : ℕ}
    (partEmb_occ : Fin (2 * K * s) ↪ Fin (nq + e_occ)) (i : Fin (2 * K * s)) :
    symEmb54 (e_sym := e_sym) partEmb_occ (Fin.castAdd e_sym i) =
      occEmb54 nq e_occ e_sym (partEmb_occ i) := by
  change Fin.addCases (partEmb_occ.trans (occEmb54 nq e_occ e_sym))
      (ancSymEmb54 nq e_occ e_sym) (Fin.castAdd e_sym i) =
    occEmb54 nq e_occ e_sym (partEmb_occ i)
  exact Fin.addCases_left i

@[simp] lemma symEmb54_natAdd {nq e_occ e_sym K s : ℕ}
    (partEmb_occ : Fin (2 * K * s) ↪ Fin (nq + e_occ)) (j : Fin e_sym) :
    symEmb54 (e_sym := e_sym) partEmb_occ (Fin.natAdd (2 * K * s) j) =
      ancSymEmb54 nq e_occ e_sym j := by
  change Fin.addCases (partEmb_occ.trans (occEmb54 nq e_occ e_sym))
      (ancSymEmb54 nq e_occ e_sym) (Fin.natAdd (2 * K * s) j) =
    ancSymEmb54 nq e_occ e_sym j
  exact Fin.addCases_right j

def degState54 (nq e_occ e_sym : ℕ) (degState_occ : ℕ → Qubits (nq + e_occ)) (k : ℕ) :
    Qubits (nq + (e_occ + e_sym)) :=
  fun a => if h : a.1 < nq + e_occ then degState_occ k ⟨a.1, h⟩ else false

lemma padKet_eq_embedPartAndDeg54_occ (nq e_occ e_sym : ℕ) (ψ : EuclideanSpace ℂ (Qubits nq)) :
    padKet (e_occ + e_sym) ψ =
      embedPartAndDeg54 (occEmb54 nq e_occ e_sym) (padKet e_occ ψ) (fun _ => false) := by
  ext z
  simp only [padKet, embedPartAndDeg54_apply]
  have hiff : (∀ j : Fin (e_occ + e_sym), z (Fin.natAdd nq j) = false) ↔
      (∀ a : Fin (nq + (e_occ + e_sym)),
        a ∉ Set.range (occEmb54 nq e_occ e_sym) → z a = false) ∧
      (∀ j : Fin e_occ, z (occEmb54 nq e_occ e_sym (Fin.natAdd nq j)) = false) := by
    constructor
    · intro h
      refine ⟨fun a ha => ?_, fun j => ?_⟩
      · have hge : nq + e_occ ≤ a.1 := by
          by_contra hlt
          exact ha ⟨⟨a.1, by omega⟩, Fin.ext rfl⟩
        have hlt := a.isLt
        have ha_eq : a = Fin.natAdd nq ⟨a.1 - nq, by omega⟩ := by ext; simp; omega
        rw [ha_eq]
        exact h _
      · have hj_eq : occEmb54 nq e_occ e_sym (Fin.natAdd nq j) =
            Fin.natAdd nq ⟨j.1, by omega⟩ := by ext; simp
        rw [hj_eq]
        exact h _
    · rintro ⟨hout, hin⟩ j
      by_cases hj : j.1 < e_occ
      · have hj_eq : Fin.natAdd nq j =
            occEmb54 nq e_occ e_sym (Fin.natAdd nq ⟨j.1, hj⟩) := by
          ext; simp
        rw [hj_eq]
        exact hin _
      · apply hout
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        change i.1 = nq + j.1 at hv
        omega
  by_cases hall : ∀ j : Fin (e_occ + e_sym), z (Fin.natAdd nq j) = false
  · obtain ⟨hout, hin⟩ := hiff.mp hall
    rw [if_pos hall, if_pos hout, if_pos hin]
    exact congrArg (WithLp.ofLp ψ) (funext fun i => by
      have hi : Fin.castAdd (e_occ + e_sym) i =
          occEmb54 nq e_occ e_sym (Fin.castAdd e_occ i) := by ext; simp
      rw [hi])
  · rw [if_neg hall]
    by_cases hout : ∀ a, a ∉ Set.range (occEmb54 nq e_occ e_sym) → z a = false
    · rw [if_pos hout]
      have hin : ¬ ∀ j : Fin e_occ, z (occEmb54 nq e_occ e_sym (Fin.natAdd nq j)) = false :=
        fun hin => hall (hiff.mpr ⟨hout, hin⟩)
      rw [if_neg hin]
    · rw [if_neg hout]

lemma embedPartAndDeg54_occ_part {nq e_occ e_sym N : ℕ}
    (partEmb_occ : Fin N ↪ Fin (nq + e_occ))
    (ψ : EuclideanSpace ℂ (Qubits N)) (degState_occ : ℕ → Qubits (nq + e_occ)) (k : ℕ) :
    embedPartAndDeg54 (occEmb54 nq e_occ e_sym)
        (embedPartAndDeg54 partEmb_occ ψ (degState_occ k)) (fun _ => false) =
      embedPartAndDeg54 (partEmb_occ.trans (occEmb54 nq e_occ e_sym))
        ψ (degState54 nq e_occ e_sym degState_occ k) := by
  ext z
  simp only [embedPartAndDeg54_apply]
  let partEmb := partEmb_occ.trans (occEmb54 nq e_occ e_sym)
  let d := degState54 nq e_occ e_sym degState_occ k
  have hiff : ((∀ a, a ∉ Set.range (occEmb54 nq e_occ e_sym) → z a = false) ∧
        (∀ b, b ∉ Set.range partEmb_occ → z (occEmb54 nq e_occ e_sym b) = degState_occ k b)) ↔
      (∀ a, a ∉ Set.range partEmb → z a = d a) := by
    constructor
    · rintro ⟨hout, hin⟩ a ha
      by_cases ha_occ : a ∈ Set.range (occEmb54 nq e_occ e_sym)
      · obtain ⟨b, rfl⟩ := ha_occ
        have hb : b ∉ Set.range partEmb_occ := fun ⟨i, hi⟩ => ha ⟨i, by simp [partEmb, hi]⟩
        have hd : d (occEmb54 nq e_occ e_sym b) = degState_occ k b := by
          simp [d, degState54, b.isLt]
        rw [hd]
        exact hin b hb
      · have hnot_lt : ¬ a.1 < nq + e_occ := fun hlt =>
          ha_occ ⟨⟨a.1, hlt⟩, Fin.ext rfl⟩
        have hd : d a = false := by simp [d, degState54, hnot_lt]
        rw [hd]
        exact hout a ha_occ
    · intro hall
      refine ⟨fun a ha => ?_, fun b hb => ?_⟩
      · have ha_part : a ∉ Set.range partEmb := fun ⟨i, hi⟩ => ha ⟨partEmb_occ i, hi⟩
        have hnot_lt : ¬ a.1 < nq + e_occ := fun hlt => ha ⟨⟨a.1, hlt⟩, Fin.ext rfl⟩
        have hd : d a = false := by simp [d, degState54, hnot_lt]
        rw [← hd]
        exact hall a ha_part
      · have hb_part : occEmb54 nq e_occ e_sym b ∉ Set.range partEmb := by
          rintro ⟨i, hi⟩
          exact hb ⟨i, (occEmb54 nq e_occ e_sym).injective hi⟩
        have hd : d (occEmb54 nq e_occ e_sym b) = degState_occ k b := by
          simp [d, degState54, b.isLt]
        rw [← hd]
        exact hall (occEmb54 nq e_occ e_sym b) hb_part
  by_cases hout : ∀ a, a ∉ Set.range (occEmb54 nq e_occ e_sym) → z a = false
  · rw [if_pos hout]
    by_cases hin : ∀ b, b ∉ Set.range partEmb_occ → z (occEmb54 nq e_occ e_sym b) = degState_occ k b
    · rw [if_pos hin, if_pos (hiff.mp ⟨hout, hin⟩)]
      rfl
    · rw [if_neg hin, if_neg (fun h => hin (hiff.mpr h).2)]
  · rw [if_neg hout, if_neg (fun h => hout (hiff.mpr h).1)]

lemma embedPartAndDeg54_part_eq_sym {nq e_occ e_sym K s : ℕ}
    (partEmb_occ : Fin (2 * K * s) ↪ Fin (nq + e_occ))
    (ψ : EuclideanSpace ℂ (Qubits (2 * K * s)))
    (degState_occ : ℕ → Qubits (nq + e_occ)) (k : ℕ) :
    embedPartAndDeg54 (partEmb_occ.trans (occEmb54 nq e_occ e_sym))
        ψ (degState54 nq e_occ e_sym degState_occ k) =
      embedPartAndDeg54 (symEmb54 (e_sym := e_sym) partEmb_occ)
        (padKet e_sym ψ) (degState54 nq e_occ e_sym degState_occ k) := by
  ext z
  simp only [embedPartAndDeg54_apply, padKet]
  let partEmb := partEmb_occ.trans (occEmb54 nq e_occ e_sym)
  let sEmb := symEmb54 (e_sym := e_sym) partEmb_occ
  let d := degState54 nq e_occ e_sym degState_occ k
  have hd_anc : ∀ j : Fin e_sym, d (ancSymEmb54 nq e_occ e_sym j) = false := fun j => by
    have hnot : ¬ (nq + e_occ + j.1 < nq + e_occ) := by omega
    simp [d, degState54, hnot]
  have hiff : (∀ a, a ∉ Set.range partEmb → z a = d a) ↔
      (∀ a, a ∉ Set.range sEmb → z a = d a) ∧
      (∀ j : Fin e_sym, z (sEmb (Fin.natAdd (2 * K * s) j)) = false) := by
    constructor
    · intro h
      refine ⟨fun a ha => h a ?_, fun j => ?_⟩
      · rintro ⟨i, hi⟩
        exact ha ⟨Fin.castAdd e_sym i, by simp [sEmb, ← hi, partEmb]⟩
      · rw [show sEmb (Fin.natAdd (2 * K * s) j) = ancSymEmb54 nq e_occ e_sym j from
            symEmb54_natAdd partEmb_occ j, ← hd_anc j]
        apply h
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        have hlt := (partEmb_occ i).isLt
        change (partEmb_occ i).1 = nq + e_occ + j.1 at hv
        omega
    · rintro ⟨hout, hin⟩ a ha
      by_cases ha_sym : a ∈ Set.range sEmb
      · obtain ⟨u, rfl⟩ := ha_sym
        induction u using Fin.addCases with
        | left i =>
          exfalso; apply ha; exact ⟨i, by simp [sEmb, partEmb]⟩
        | right j =>
          rw [show sEmb (Fin.natAdd (2 * K * s) j) = ancSymEmb54 nq e_occ e_sym j from
              symEmb54_natAdd partEmb_occ j, hd_anc j, ← symEmb54_natAdd partEmb_occ j]
          exact hin j
      · exact hout a ha_sym
  by_cases hall : ∀ a, a ∉ Set.range partEmb → z a = d a
  · obtain ⟨hout, hin⟩ := hiff.mp hall
    rw [if_pos hall, if_pos hout, if_pos hin]
    exact congrArg (WithLp.ofLp ψ) (funext fun i => by simp)
  · rw [if_neg hall]
    by_cases hout : ∀ a, a ∉ Set.range sEmb → z a = d a
    · rw [if_pos hout]
      have hin : ¬ ∀ j : Fin e_sym, z (sEmb (Fin.natAdd (2 * K * s) j)) = false :=
        fun hin => hall (hiff.mpr ⟨hout, hin⟩)
      rw [if_neg hin]
    · rw [if_neg hout]

lemma theorem_5_4_from_occ_and_sym
    (C_occ : ℝ) (hC_occ : 0 < C_occ) (K_occ : ℕ)
    (hocc : ∀ (n K D q : ℕ), 1 ≤ n → 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
      let s := Nat.clog 2 n + 1
      ∃ (e_occ : ℕ) (partEmb_occ : Fin (2 * K * s) ↪ Fin (n * q + e_occ))
        (degState_occ : ℕ → Qubits (n * q + e_occ))
        (V_occ : Circuit gates12 (n * q + e_occ)),
        (V_occ.size : ℝ) ≤ C_occ * n * (q + Nat.clog 2 (n * D + 2) + 1) +
          C_occ * (n + K * s) * (Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1) ^ K_occ ∧
        ∀ (α : Fin n → ℕ) (_hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K),
          ∃ l : Fin (2 * K) → Fin (n + 1),
            Monotone l ∧
            (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) ∧
            (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i ∧
            act V_occ.unitary (padKet e_occ (ket (flatReg n q fun i => natToBits q (α i)))) =
              embedPartAndDeg54 partEmb_occ
                (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))
                (degState_occ (∑ i, α i)))
    (C_sym : ℝ) (hC_sym : 0 < C_sym) (K_sym : ℕ)
    (hsym : ∀ (n K : ℕ), 1 ≤ n → 1 ≤ K →
      let s := Nat.clog 2 n + 1
      ∃ (e_sym : ℕ) (V_sym : Circuit gates12 (2 * K * s + e_sym)),
        ((V_sym.size : ℕ) : ℝ) ≤
          C_sym * ((K * s : ℕ) : ℝ) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym ∧
        ∀ (α : Fin n → ℕ) (hk : K ≤ ∑ i, α i ∧ ∑ i, α i ≤ 2 * K)
          (l : Fin (2 * K) → Fin (n + 1)),
          Monotone l →
          (∀ i : Fin n, (Finset.univ.filter fun p => l p = ⟨i.1, by omega⟩).card = α i) →
          (Finset.univ.filter fun p => l p = ⟨n, Nat.lt_succ_self n⟩).card = 2 * K - ∑ i, α i →
          act V_sym.unitary (padKet e_sym (ket (flatReg (2 * K) s fun p => particleSym54 n s (l p)))) =
            padKet e_sym (multinomKet54 n s K α hk)) :
    ∃ C : ℝ, 0 < C ∧ ∃ K' : ℕ,
      ∀ (n K D q : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        ∃ (s e r : ℕ) (V : Circuit gates12 (n * q + e)) (W : Qubits r → Circuit gates12 (n * q + e))
          (meas : Fin r ↪ Fin (n * q + e)) (out : Fin (K * s) ↪ Fin (n * q + e)),
          n ≤ 2 ^ s ∧ (r : ℝ) ≤ C * K ∧
          (∀ t : Qubits r, ((V.size + (W t).size : ℕ) : ℝ) ≤
            C * n * (Real.log (2 ^ q) + Real.log (n * D)) +
              C * (n + K * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K') ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            measChannelOut V.unitary (fun t => (W t).unitary) meas out
              (padKet e (bandKet n q K w)) = dirTensorPow s K w := by
  let C_V : ℝ := C_occ + C_sym
  let K_V : ℕ := max K_occ K_sym
  refine theorem_5_4_from_sym_witness C_V (by positivity) K_V fun n K D q hn hK hD hq => ?_
  let s : ℕ := Nat.clog 2 n + 1
  obtain ⟨e_occ, partEmb_occ, degState_occ, V_occ, hVocc_size, hVocc_act⟩ :=
    hocc n K D q hn hK hD hq
  obtain ⟨e_sym, V_sym, hVsym_size, hVsym_act⟩ := hsym n K hn hK
  let occEmb := occEmb54 (n * q) e_occ e_sym
  let sEmb := symEmb54 (e_sym := e_sym) partEmb_occ
  let partEmb := partEmb_occ.trans occEmb
  let V : Circuit gates12 (n * q + (e_occ + e_sym)) :=
    embedCircuit54 occEmb V_occ ++ embedCircuit54 sEmb V_sym
  let degState := degState54 (n * q) e_occ e_sym degState_occ
  refine ⟨e_occ + e_sym, V, partEmb, degState, ?_, ?_⟩
  · have hVsize : (V.size : ℝ) = (V_occ.size : ℝ) + (V_sym.size : ℝ) := by
      dsimp only [V]
      change (((embedCircuit54 occEmb V_occ ++ embedCircuit54 sEmb V_sym).length : ℕ) : ℝ) = _
      rw [List.length_append]
      have h1 : (embedCircuit54 occEmb V_occ).length = V_occ.size := embedCircuit54_size _ _
      have h2 : (embedCircuit54 sEmb V_sym).length = V_sym.size := embedCircuit54_size _ _
      rw [h1, h2]
      push_cast; rfl
    have hlog_ge1 : (1 : ℝ) ≤ (Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) := by
      exact_mod_cast Nat.succ_pos _
    have hpow_occ : ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_occ ≤
        ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V :=
      pow_le_pow_right₀ hlog_ge1 (le_max_left _ _)
    have hpow_sym : ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym ≤
        ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V :=
      pow_le_pow_right₀ hlog_ge1 (le_max_right _ _)
    have hocc_norm : (V_occ.size : ℝ) ≤
        C_occ * (n : ℝ) * ((q : ℝ) + ((Nat.clog 2 (n * D + 2) + 1 : ℕ) : ℝ)) +
        C_occ * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_occ := by
      simpa [s, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc] using hVocc_size
    have hocc' : (V_occ.size : ℝ) ≤ C_occ * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) +
        C_occ * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V := by
      have hmul : C_occ * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_occ ≤
          C_occ * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V :=
        mul_le_mul_of_nonneg_left hpow_occ (by positivity)
      linarith
    have hsym_norm : (V_sym.size : ℝ) ≤
        C_sym * ((K : ℝ) * (s : ℝ)) *
          ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym := by
      simpa [s, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hVsym_size
    have hsym' : (V_sym.size : ℝ) ≤ C_sym * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
        ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V := by
      have hKs_le : (K : ℝ) * (s : ℝ) ≤ (n : ℝ) + (K : ℝ) * (s : ℝ) := by
        have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have h1 : C_sym * ((K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_sym ≤
          C_sym * ((n : ℝ) + (K : ℝ) * (s : ℝ)) *
            ((Nat.clog 2 ((K + 1) * (n + 1) + 2) + 1 : ℕ) : ℝ) ^ K_V :=
        mul_le_mul (mul_le_mul_of_nonneg_left hKs_le hC_sym.le) hpow_sym (by positivity) (by positivity)
      exact le_trans hsym_norm h1
    have hnq_nn : 0 ≤ (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) := by positivity
    have hfirst : C_occ * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) ≤
        C_V * (n : ℝ) * ((q : ℝ) + (Nat.clog 2 (n * D + 2) + 1 : ℕ)) := by
      have hC : C_occ ≤ C_V := by dsimp [C_V]; linarith
      have := mul_le_mul_of_nonneg_right hC hnq_nn
      linarith
    rw [hVsize]
    dsimp [C_V] at hfirst ⊢
    linarith
  · intro α hk
    obtain ⟨l, hl_mono, hl_occ, hl_blank, hVocc_ket⟩ := hVocc_act α hk
    have hVsym_ket := hVsym_act α hk l hl_mono hl_occ hl_blank
    have hunit : V.unitary = embedOp V_sym.unitary sEmb * embedOp V_occ.unitary occEmb := by
      dsimp only [V]
      rw [circuit_unitary_append, embedCircuit54_unitary, embedCircuit54_unitary]
    rw [hunit, act_mul, padKet_eq_embedPartAndDeg54_occ, act_embedOp_embedPartAndDeg54,
      hVocc_ket, embedPartAndDeg54_occ_part, embedPartAndDeg54_part_eq_sym,
      act_embedOp_embedPartAndDeg54, hVsym_ket, ← embedPartAndDeg54_part_eq_sym]

end Aux_Thm54

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ K' : ℕ,
      ∀ (n K D q : ℕ), 1 ≤ K → 2 * K + 1 ≤ D → D ≤ 2 ^ q →
        ∃ (s e r : ℕ) (V : Circuit gates12 (n * q + e)) (W : Qubits r → Circuit gates12 (n * q + e))
          (meas : Fin r ↪ Fin (n * q + e)) (out : Fin (K * s) ↪ Fin (n * q + e)),
          n ≤ 2 ^ s ∧ (r : ℝ) ≤ C * K ∧
          (∀ t : Qubits r, ((V.size + (W t).size : ℕ) : ℝ) ≤
            C * n * (Real.log (2 ^ q) + Real.log (n * D)) +
              C * (n + K * Real.log (n + 1)) * Real.log ((K + 1) * (n + 1)) ^ K') ∧
          ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
            measChannelOut V.unitary (fun t => (W t).unitary) meas out
              (padKet e (bandKet n q K w)) = dirTensorPow s K w := by
  obtain ⟨C_occ, K_occ, hC_occ, hocc⟩ := occupation_to_nsil_54
  obtain ⟨C_sym, hC_sym, K_sym, hsym⟩ := nsil_symmetrize_54
  exact Aux_Thm54.theorem_5_4_from_occ_and_sym C_occ hC_occ K_occ hocc C_sym hC_sym K_sym hsym

