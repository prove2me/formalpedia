-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P06.bounded_normal_form_index_count
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-21T00:18:06.131313+00:00
-- url     : https://prove2.me/submissions/073c1f64-1ae9-4661-aca1-6c6a2ca1a365

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P06
noncomputable section

open scoped BigOperators Classical TensorProduct
open Fin
attribute [local instance] Classical.propDecidable Classical.decEq
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace QAlgorithms.Papers.Independent.Intake100.P06

open QAlgorithms.Papers.Independent.Support21.P14

def AuxBN_eraseFun {m : ℕ} (p : Fin (m + 1)) (i : Fin m) : {i : Fin (m + 1) // i ≠ p} :=
  ⟨p.succAbove i, succAbove_ne p i⟩

theorem AuxBN_erase_inj {m : ℕ} (p : Fin (m + 1)) :
    Function.Injective (AuxBN_eraseFun p) := by
  intro a b h
  exact succAbove_right_injective (Subtype.ext_iff.mp h)

theorem AuxBN_erase_surj {m : ℕ} (p : Fin (m + 1)) :
    Function.Surjective (AuxBN_eraseFun p) := by
  intro x
  obtain ⟨z, hz⟩ := exists_succAbove_eq x.property
  exact ⟨z, Subtype.ext hz⟩

def AuxBN_erase {m : ℕ} (p : Fin (m + 1)) :
    Fin m ≃ {i : Fin (m + 1) // i ≠ p} :=
  Equiv.ofBijective (AuxBN_eraseFun p) ⟨AuxBN_erase_inj p, AuxBN_erase_surj p⟩

theorem AuxBN_two_succ (n : ℕ) : 2 * (n + 1) = 2 * n + 2 := by ring

def AuxBN_ground (n : ℕ) : Fin (2 * (n + 1)) ≃ Fin (2 * n + 2) :=
  finCongr (AuxBN_two_succ n)

theorem AuxBN_odd_zero : oddPairingCount 0 = 1 := by
  simp [oddPairingCount]

theorem AuxBN_odd_succ (n : ℕ) :
    oddPairingCount (n + 1) = (2 * n + 1) * oddPairingCount n := by
  unfold oddPairingCount
  rw [Finset.prod_range_succ, mul_comm]

instance AuxBN_fintype_pairing (n : ℕ) : Fintype (BrauerPairing n) :=
  Subtype.fintype _

instance AuxBN_finite_pairing (n : ℕ) : Finite (BrauerPairing n) :=
  inferInstance

theorem AuxBN_strands_card (n : ℕ) (p : BrauerPairing n) :
    Nat.card {i : Fin (2 * n) // i < p.val i} = n := by
  let lo := {i : Fin (2 * n) // i < p.val i}
  let hi := {i : Fin (2 * n) // p.val i < i}
  have hinvol : Function.Involutive p.val := p.property.1
  have hne : ∀ i, p.val i ≠ i := p.property.2
  let e : lo ≃ hi :=
    { toFun := fun x =>
        ⟨p.val x.1, by
          have hx : x.1 < p.val x.1 := x.2
          have hx' : p.val (p.val x.1) = x.1 := hinvol x.1
          have : p.val (p.val x.1) < p.val x.1 := by simpa [hx'] using hx
          exact this⟩
      invFun := fun y =>
        ⟨p.val y.1, by
          have hy : p.val y.1 < y.1 := y.2
          have hy' : p.val (p.val y.1) = y.1 := hinvol y.1
          have : p.val y.1 < p.val (p.val y.1) := by simpa [hy'] using hy
          exact this⟩
      left_inv := fun x => Subtype.ext (hinvol x.1)
      right_inv := fun y => Subtype.ext (hinvol y.1) }
  have hsplit : ∀ i : Fin (2 * n), i < p.val i ∨ p.val i < i := by
    intro i
    exact (lt_or_gt_of_ne (hne i).symm)
  let split : Fin (2 * n) ≃ lo ⊕ hi :=
    { toFun := fun i =>
        if h : i < p.val i then Sum.inl ⟨i, h⟩
        else
          Sum.inr ⟨i, by
            rcases hsplit i with h' | h'
            · exact (h h').elim
            · exact h'⟩
      invFun := fun s =>
        match s with
        | Sum.inl x => x.1
        | Sum.inr y => y.1
      left_inv := by
        intro i
        by_cases h : i < p.val i
        · simp [h]
        · simp [h]
      right_inv := by
        intro s
        cases s with
        | inl x =>
          simp [x.2]
        | inr y =>
          have : ¬ y.1 < p.val y.1 := not_lt.mpr (le_of_lt y.2)
          simp [this] }
  have hsum : Nat.card (lo ⊕ hi) = Nat.card lo + Nat.card hi := Nat.card_sum
  have hfin : Nat.card (Fin (2 * n)) = 2 * n := Nat.card_fin (2 * n)
  have hcong : Nat.card (Fin (2 * n)) = Nat.card (lo ⊕ hi) := Nat.card_congr split
  have heq : Nat.card lo = Nat.card hi := Nat.card_congr e
  have : 2 * Nat.card lo = 2 * n := by
    linarith
  exact Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 2) this

theorem AuxBN_erase0_val {n : ℕ} (k : Fin (2 * n + 2)) (hk : k ≠ 0)
    (j : Fin (2 * n + 1)) :
    ((AuxBN_erase (0 : Fin (2 * n + 2))) j).1 = k ↔
      j = (AuxBN_erase (0 : Fin (2 * n + 2))).symm ⟨k, hk⟩ := by
  constructor
  · intro h
    have : AuxBN_erase (0 : Fin (2 * n + 2)) j = ⟨k, hk⟩ := Subtype.ext h
    exact (Equiv.apply_eq_iff_eq_symm_apply (AuxBN_erase (0 : Fin (2 * n + 2)))).1 this
  · intro h
    rw [h, Equiv.apply_symm_apply]

def AuxBN_rest {n : ℕ} (k : Fin (2 * n + 2)) (hk : k ≠ 0) :
    Fin (2 * n) ≃ {i : Fin (2 * n + 2) // i ≠ 0 ∧ i ≠ k} :=
  let e0 := AuxBN_erase (0 : Fin (2 * n + 2))
  let k0 : Fin (2 * n + 1) := e0.symm ⟨k, hk⟩
  let e1 := AuxBN_erase k0
  { toFun := fun x =>
      let y := e1 x
      ⟨(e0 y.1).1, by
        constructor
        · exact (e0 y.1).2
        · intro h
          have : y.1 = k0 := (AuxBN_erase0_val k hk y.1).1 h
          exact y.2 this⟩
    invFun := fun z =>
      e1.symm ⟨e0.symm ⟨z.1, z.2.1⟩, by
        intro h
        apply z.2.2
        have h1 : (e0 (e0.symm ⟨z.1, z.2.1⟩)).1 = (e0 k0).1 :=
          congrArg (fun t => (e0 t).1) h
        rw [Equiv.apply_symm_apply] at h1
        have h2 : (e0 k0).1 = k := by
          dsimp [k0]
          rw [Equiv.apply_symm_apply]
        exact h1.trans h2⟩
    left_inv := by
      intro x
      dsimp
      have : (⟨(e0 (e1 x).1).1, (e0 (e1 x).1).2⟩ : {i : Fin (2 * n + 2) // i ≠ 0}) =
          e0 (e1 x).1 := Subtype.ext rfl
      -- after invFun's e0.symm, this becomes e1 x, then e1.symm
      simp [this]
    right_inv := by
      intro z
      dsimp
      apply Subtype.ext
      simp }

theorem AuxBN_rest_val_congr {n : ℕ} {k₁ k₂ : Fin (2 * n + 2)}
    (h : k₁ = k₂) (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) (x : Fin (2 * n)) :
    ((AuxBN_rest k₁ h₁) x).1 = ((AuxBN_rest k₂ h₂) x).1 := by
  cases h
  rfl

theorem AuxBN_rest_symm_val_congr {n : ℕ} {k₁ k₂ : Fin (2 * n + 2)}
    (h : k₁ = k₂) (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0)
    (z : Fin (2 * n + 2)) (hz₁ : z ≠ 0 ∧ z ≠ k₁) (hz₂ : z ≠ 0 ∧ z ≠ k₂) :
    (AuxBN_rest k₁ h₁).symm ⟨z, hz₁⟩ = (AuxBN_rest k₂ h₂).symm ⟨z, hz₂⟩ := by
  cases h
  rfl

def AuxBN_conj {n : ℕ} (p : BrauerPairing (n + 1)) :
    Fin (2 * n + 2) → Fin (2 * n + 2) :=
  fun i => AuxBN_ground n (p.1 ((AuxBN_ground n).symm i))

theorem AuxBN_conj_involutive {n : ℕ} (p : BrauerPairing (n + 1)) :
    Function.Involutive (AuxBN_conj p) := by
  intro i
  dsimp [AuxBN_conj]
  rw [Equiv.symm_apply_apply, p.property.1, Equiv.apply_symm_apply]

theorem AuxBN_conj_nofix {n : ℕ} (p : BrauerPairing (n + 1)) :
    ∀ i : Fin (2 * n + 2), AuxBN_conj p i ≠ i := by
  intro i hi
  apply p.property.2 ((AuxBN_ground n).symm i)
  dsimp [AuxBN_conj] at hi
  exact (AuxBN_ground n).injective (by
    rw [Equiv.apply_symm_apply]
    exact hi)

def AuxBN_restrict (n : ℕ) (p : BrauerPairing (n + 1)) : BrauerPairing n :=
  let p' := AuxBN_conj p
  let hk : p' 0 ≠ 0 := AuxBN_conj_nofix p 0
  let e := AuxBN_rest (p' 0) hk
  have hinvol : Function.Involutive p' := AuxBN_conj_involutive p
  have hrem : ∀ x : Fin (2 * n), p' (e x).1 ≠ 0 ∧ p' (e x).1 ≠ p' 0 := by
    intro x
    constructor
    · intro h
      have : (e x).1 = p' 0 := by
        calc
          (e x).1 = p' (p' (e x).1) := (hinvol _).symm
          _ = p' 0 := by rw [h]
      exact (e x).2.2 this
    · intro h
      have : (e x).1 = 0 := by
        calc
          (e x).1 = p' (p' (e x).1) := (hinvol _).symm
          _ = p' (p' 0) := by rw [h]
          _ = 0 := hinvol 0
      exact (e x).2.1 this
  ⟨fun x => e.symm ⟨p' (e x).1, hrem x⟩,
    by
      intro x
      have hx := hrem x
      have hx2 := hrem (e.symm ⟨p' (e x).1, hx⟩)
      apply e.injective
      apply Subtype.ext
      have h1 : e (e.symm ⟨p' (e x).1, hx⟩) = ⟨p' (e x).1, hx⟩ :=
        Equiv.apply_symm_apply e _
      calc
        (e (e.symm ⟨p' (e (e.symm ⟨p' (e x).1, hx⟩)).1, hx2⟩)).1
            = p' (e (e.symm ⟨p' (e x).1, hx⟩)).1 := by
              rw [Equiv.apply_symm_apply]
        _ = p' (p' (e x).1) := by rw [h1]
        _ = (e x).1 := hinvol (e x).1
    ,
    by
      intro x hxeq
      have hx := hrem x
      have : e (e.symm ⟨p' (e x).1, hx⟩) = e x := congrArg e hxeq
      rw [Equiv.apply_symm_apply] at this
      exact AuxBN_conj_nofix p (e x).1 (Subtype.ext_iff.mp this)⟩

theorem AuxBN_restrict_apply (n : ℕ) (p : BrauerPairing (n + 1)) (x : Fin (2 * n)) :
    (AuxBN_restrict n p).1 x =
      (AuxBN_rest (AuxBN_conj p 0) (AuxBN_conj_nofix p 0)).symm
        ⟨AuxBN_conj p ((AuxBN_rest (AuxBN_conj p 0) (AuxBN_conj_nofix p 0)) x).1,
          (by
            have hinvol : Function.Involutive (AuxBN_conj p) := AuxBN_conj_involutive p
            let e := AuxBN_rest (AuxBN_conj p 0) (AuxBN_conj_nofix p 0)
            constructor
            · intro h
              have : (e x).1 = AuxBN_conj p 0 := by
                calc
                  (e x).1 = AuxBN_conj p (AuxBN_conj p (e x).1) := (hinvol _).symm
                  _ = AuxBN_conj p 0 := by rw [h]
              exact (e x).2.2 this
            · intro h
              have : (e x).1 = 0 := by
                calc
                  (e x).1 = AuxBN_conj p (AuxBN_conj p (e x).1) := (hinvol _).symm
                  _ = AuxBN_conj p (AuxBN_conj p 0) := by rw [h]
                  _ = 0 := hinvol 0
              exact (e x).2.1 this)⟩ :=
  rfl

def AuxBN_partner (n : ℕ) (p : BrauerPairing (n + 1)) : Fin (2 * n + 1) :=
  (AuxBN_erase (0 : Fin (2 * n + 2))).symm ⟨AuxBN_conj p 0, AuxBN_conj_nofix p 0⟩

theorem AuxBN_partner_val (n : ℕ) (p : BrauerPairing (n + 1)) :
    ((AuxBN_erase (0 : Fin (2 * n + 2))) (AuxBN_partner n p)).1 = AuxBN_conj p 0 := by
  unfold AuxBN_partner
  rw [Equiv.apply_symm_apply]

def AuxBN_extendFun (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    Fin (2 * n + 2) → Fin (2 * n + 2) :=
  let k := (AuxBN_erase (0 : Fin (2 * n + 2))) t
  let e := AuxBN_rest k.1 k.2
  fun i =>
    if hi0 : i = 0 then k.1
    else if hik : i = k.1 then 0
    else (e (q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩))).1

theorem AuxBN_extendFun_zero (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    AuxBN_extendFun n t q 0 = ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1 := by
  simp [AuxBN_extendFun]

theorem AuxBN_extendFun_k (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    AuxBN_extendFun n t q ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1 = 0 := by
  dsimp [AuxBN_extendFun]
  have hk0 : ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1 ≠ 0 :=
    ((AuxBN_erase (0 : Fin (2 * n + 2))) t).2
  simp [hk0]

theorem AuxBN_extendFun_rest (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n)
    {i : Fin (2 * n + 2)} (h0 : i ≠ 0)
    (hk : i ≠ ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1) :
    AuxBN_extendFun n t q i =
      ((AuxBN_rest ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1
          ((AuxBN_erase (0 : Fin (2 * n + 2))) t).2)
        (q.1 ((AuxBN_rest ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1
            ((AuxBN_erase (0 : Fin (2 * n + 2))) t).2).symm ⟨i, ⟨h0, hk⟩⟩))).1 := by
  dsimp [AuxBN_extendFun]
  simp [h0, hk]

theorem AuxBN_extendFun_involutive (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    Function.Involutive (AuxBN_extendFun n t q) := by
  intro i
  let k := (AuxBN_erase (0 : Fin (2 * n + 2))) t
  let e := AuxBN_rest k.1 k.2
  have hk0 : k.1 ≠ 0 := k.2
  by_cases hi0 : i = 0
  · subst hi0
    rw [AuxBN_extendFun_zero, AuxBN_extendFun_k]
  · by_cases hik : i = k.1
    · subst hik
      rw [AuxBN_extendFun_k, AuxBN_extendFun_zero]
    · rw [AuxBN_extendFun_rest n t q hi0 hik]
      have hmem :
          (e (q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩))).1 ≠ 0 ∧
            (e (q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩))).1 ≠ k.1 :=
        (e (q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩))).2
      rw [AuxBN_extendFun_rest n t q hmem.1 hmem.2]
      have hsym :
          e.symm ⟨(e (q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩))).1, ⟨hmem.1, hmem.2⟩⟩ =
            q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩) :=
        Equiv.symm_apply_apply e _
      rw [hsym, q.property.1, Equiv.apply_symm_apply]

theorem AuxBN_extendFun_nofix (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    ∀ i, AuxBN_extendFun n t q i ≠ i := by
  intro i
  let k := (AuxBN_erase (0 : Fin (2 * n + 2))) t
  let e := AuxBN_rest k.1 k.2
  have hk0 : k.1 ≠ 0 := k.2
  by_cases hi0 : i = 0
  · subst hi0
    rw [AuxBN_extendFun_zero]
    exact hk0
  · by_cases hik : i = k.1
    · subst hik
      rw [AuxBN_extendFun_k]
      exact hk0.symm
    · rw [AuxBN_extendFun_rest n t q hi0 hik]
      intro h
      have : q.1 (e.symm ⟨i, ⟨hi0, hik⟩⟩) = e.symm ⟨i, ⟨hi0, hik⟩⟩ := by
        apply e.injective
        apply Subtype.ext
        rw [Equiv.apply_symm_apply]
        exact h
      exact q.property.2 _ this

def AuxBN_extend (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    BrauerPairing (n + 1) :=
  ⟨fun i => (AuxBN_ground n).symm (AuxBN_extendFun n t q (AuxBN_ground n i)),
    by
      intro i
      dsimp
      rw [Equiv.apply_symm_apply, AuxBN_extendFun_involutive, Equiv.symm_apply_apply]
    ,
    by
      intro i hi
      apply AuxBN_extendFun_nofix n t q (AuxBN_ground n i)
      dsimp at hi
      calc
        AuxBN_extendFun n t q (AuxBN_ground n i)
            = AuxBN_ground n
                ((AuxBN_ground n).symm (AuxBN_extendFun n t q (AuxBN_ground n i))) := by
              rw [Equiv.apply_symm_apply]
        _ = AuxBN_ground n i := by rw [hi]⟩

theorem AuxBN_conj_extend (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    AuxBN_conj (AuxBN_extend n t q) = AuxBN_extendFun n t q := by
  ext i
  dsimp [AuxBN_conj, AuxBN_extend]
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem AuxBN_extend_partner (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    AuxBN_partner n (AuxBN_extend n t q) = t := by
  unfold AuxBN_partner
  have h :
      (⟨AuxBN_conj (AuxBN_extend n t q) 0, AuxBN_conj_nofix (AuxBN_extend n t q) 0⟩ :
          {i : Fin (2 * n + 2) // i ≠ 0}) =
        (AuxBN_erase (0 : Fin (2 * n + 2))) t := by
    apply Subtype.ext
    change AuxBN_conj (AuxBN_extend n t q) 0 = ((AuxBN_erase (0 : Fin (2 * n + 2))) t).1
    rw [congrFun (AuxBN_conj_extend n t q) 0, AuxBN_extendFun_zero]
  rw [h, Equiv.symm_apply_apply]

theorem AuxBN_extend_restrict (n : ℕ) (t : Fin (2 * n + 1)) (q : BrauerPairing n) :
    AuxBN_restrict n (AuxBN_extend n t q) = q := by
  apply Subtype.ext
  funext x
  set p := AuxBN_extend n t q
  set k := AuxBN_erase (0 : Fin (2 * n + 2)) t
  have hp0 : AuxBN_conj p 0 = k.1 := by
    change AuxBN_conj (AuxBN_extend n t q) 0 = k.1
    rw [congrFun (AuxBN_conj_extend n t q) 0, AuxBN_extendFun_zero]
  set e_c := AuxBN_rest (AuxBN_conj p 0) (AuxBN_conj_nofix p 0)
  set e_k := AuxBN_rest k.1 k.2
  have hvalx : (e_c x).1 = (e_k x).1 :=
    AuxBN_rest_val_congr hp0 (AuxBN_conj_nofix p 0) k.2 x
  have hx0c : (e_c x).1 ≠ 0 := (e_c x).2.1
  have hxk : (e_c x).1 ≠ k.1 := by
    rw [hvalx]
    exact (e_k x).2.2
  apply e_c.injective
  apply Subtype.ext
  -- Reduce to an equality of first components, avoiding dependent rewrites.
  have hr' : (e_c ((AuxBN_restrict n p).1 x)).1 = AuxBN_conj p (e_c x).1 := by
    rw [AuxBN_restrict_apply n p x]
    simp [e_c]
  rw [hr']
  have hpt : AuxBN_conj p (e_c x).1 = AuxBN_extendFun n t q (e_c x).1 :=
    congrFun (AuxBN_conj_extend n t q) _
  rw [hpt, AuxBN_extendFun_rest n t q hx0c hxk]
  have hss : e_k.symm ⟨(e_c x).1, ⟨hx0c, hxk⟩⟩ = x := by
    have h := AuxBN_rest_symm_val_congr hp0.symm k.2 (AuxBN_conj_nofix p 0)
      (e_c x).1 ⟨hx0c, hxk⟩ (e_c x).2
    rw [h, Equiv.symm_apply_apply]
  rw [hss]
  exact (AuxBN_rest_val_congr hp0.symm k.2 (AuxBN_conj_nofix p 0) (q.1 x)).symm

theorem AuxBN_extendFun_eq_conj_of_restrict (n : ℕ) (p : BrauerPairing (n + 1))
    (j : Fin (2 * n + 2)) :
    AuxBN_extendFun n (AuxBN_partner n p) (AuxBN_restrict n p) j =
      AuxBN_conj p j := by
  have hk : ((AuxBN_erase (0 : Fin (2 * n + 2))) (AuxBN_partner n p)).1 =
      AuxBN_conj p 0 := AuxBN_partner_val n p
  by_cases h0 : j = 0
  · rw [h0, AuxBN_extendFun_zero, hk]
  · by_cases hkj : j = ((AuxBN_erase (0 : Fin (2 * n + 2))) (AuxBN_partner n p)).1
    · rw [hkj, AuxBN_extendFun_k, hk, AuxBN_conj_involutive]
    · have hkj' : j ≠ AuxBN_conj p 0 := fun h => hkj (h.trans hk.symm)
      rw [AuxBN_extendFun_rest n (AuxBN_partner n p) (AuxBN_restrict n p) h0 hkj]
      set k := AuxBN_erase (0 : Fin (2 * n + 2)) (AuxBN_partner n p)
      set e_k := AuxBN_rest k.1 k.2
      set e_c := AuxBN_rest (AuxBN_conj p 0) (AuxBN_conj_nofix p 0)
      set x := e_k.symm ⟨j, ⟨h0, hkj⟩⟩
      have hxc : x = e_c.symm ⟨j, ⟨h0, hkj'⟩⟩ :=
        AuxBN_rest_symm_val_congr hk k.2 (AuxBN_conj_nofix p 0) j ⟨h0, hkj⟩ ⟨h0, hkj'⟩
      have hec_x : (e_c x).1 = j := by
        rw [hxc, Equiv.apply_symm_apply]
      have hcj0 : AuxBN_conj p j ≠ 0 := by
        intro h
        have : j = AuxBN_conj p 0 := by
          calc
            j = AuxBN_conj p (AuxBN_conj p j) := (AuxBN_conj_involutive p j).symm
            _ = AuxBN_conj p 0 := by rw [h]
        exact hkj' this
      have hcj_c0 : AuxBN_conj p j ≠ AuxBN_conj p 0 := by
        intro h
        exact h0 ((AuxBN_conj_involutive p).injective h)
      have hr := AuxBN_restrict_apply n p x
      -- compare values after applying e_k
      change (e_k ((AuxBN_restrict n p).1 x)).1 = AuxBN_conj p j
      apply Eq.trans (congrArg (fun y => (e_k y).1) hr)
      have hinner :
          (⟨AuxBN_conj p (e_c x).1, (by
              have hinvol : Function.Involutive (AuxBN_conj p) := AuxBN_conj_involutive p
              constructor
              · intro h
                have : (e_c x).1 = AuxBN_conj p 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p 0 := by rw [h]
                exact (e_c x).2.2 this
              · intro h
                have : (e_c x).1 = 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p (AuxBN_conj p 0) := by rw [h]
                    _ = 0 := hinvol 0
                exact (e_c x).2.1 this)⟩ :
              {i : Fin (2 * n + 2) // i ≠ 0 ∧ i ≠ AuxBN_conj p 0}) =
            ⟨AuxBN_conj p j, ⟨hcj0, hcj_c0⟩⟩ := by
        apply Subtype.ext
        exact congrArg (AuxBN_conj p) hec_x
      have hsym :
          e_c.symm ⟨AuxBN_conj p (e_c x).1, (by
              have hinvol : Function.Involutive (AuxBN_conj p) := AuxBN_conj_involutive p
              constructor
              · intro h
                have : (e_c x).1 = AuxBN_conj p 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p 0 := by rw [h]
                exact (e_c x).2.2 this
              · intro h
                have : (e_c x).1 = 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p (AuxBN_conj p 0) := by rw [h]
                    _ = 0 := hinvol 0
                exact (e_c x).2.1 this)⟩ =
            e_c.symm ⟨AuxBN_conj p j, ⟨hcj0, hcj_c0⟩⟩ := by
        congr 1
      -- restrict_apply uses exactly this e_c.symm term
      -- After congrArg hr, LHS is (e_k (e_c.symm ⟨conj p (e_c x).1, _⟩)).1
      -- We rewrite via hsym, then compare e_k vs e_c
      have hval := AuxBN_rest_val_congr hk k.2 (AuxBN_conj_nofix p 0)
        (e_c.symm ⟨AuxBN_conj p j, ⟨hcj0, hcj_c0⟩⟩)
      -- Need to change the current LHS to (e_k (e_c.symm ⟨conj p j⟩)).1
      -- hr's RHS is definitionally e_c.symm ⟨...⟩, so:
      calc
        (e_k (e_c.symm ⟨AuxBN_conj p (e_c x).1, (by
              have hinvol : Function.Involutive (AuxBN_conj p) := AuxBN_conj_involutive p
              constructor
              · intro h
                have : (e_c x).1 = AuxBN_conj p 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p 0 := by rw [h]
                exact (e_c x).2.2 this
              · intro h
                have : (e_c x).1 = 0 := by
                  calc
                    (e_c x).1 = AuxBN_conj p (AuxBN_conj p (e_c x).1) := (hinvol _).symm
                    _ = AuxBN_conj p (AuxBN_conj p 0) := by rw [h]
                    _ = 0 := hinvol 0
                exact (e_c x).2.1 this)⟩)).1
            = (e_k (e_c.symm ⟨AuxBN_conj p j, ⟨hcj0, hcj_c0⟩⟩)).1 := by
              rw [hsym]
        _ = (e_c (e_c.symm ⟨AuxBN_conj p j, ⟨hcj0, hcj_c0⟩⟩)).1 := hval
        _ = AuxBN_conj p j := by rw [Equiv.apply_symm_apply]

theorem AuxBN_restrict_extend (n : ℕ) (p : BrauerPairing (n + 1)) :
    AuxBN_extend n (AuxBN_partner n p) (AuxBN_restrict n p) = p := by
  apply Subtype.ext
  funext i
  dsimp [AuxBN_extend]
  rw [AuxBN_extendFun_eq_conj_of_restrict]
  dsimp [AuxBN_conj]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

def AuxBN_succEquiv (n : ℕ) :
    BrauerPairing (n + 1) ≃ Fin (2 * n + 1) × BrauerPairing n :=
  { toFun := fun p => (AuxBN_partner n p, AuxBN_restrict n p)
    invFun := fun z => AuxBN_extend n z.1 z.2
    left_inv := fun p => AuxBN_restrict_extend n p
    right_inv := fun z =>
      Prod.ext (AuxBN_extend_partner n z.1 z.2) (AuxBN_extend_restrict n z.1 z.2) }

theorem AuxBN_pairing_zero : Nat.card (BrauerPairing 0) = 1 := by
  let u : BrauerPairing 0 := ⟨id, fun _ => rfl, fun i => i.elim0⟩
  have : Unique (BrauerPairing 0) :=
    { default := u
      uniq := by
        intro p
        apply Subtype.ext
        funext i
        exact i.elim0 }
  exact Nat.card_unique

theorem AuxBN_pairing_card : ∀ n, Nat.card (BrauerPairing n) = oddPairingCount n
  | 0 => by rw [AuxBN_pairing_zero, AuxBN_odd_zero]
  | n + 1 => by
    have h := Nat.card_congr (AuxBN_succEquiv n)
    rw [Nat.card_prod, Nat.card_fin] at h
    rw [h, AuxBN_pairing_card n, AuxBN_odd_succ, mul_comm]

theorem AuxBN_label_card (n r : ℕ) (p : BrauerPairing n) :
    Nat.card ({i : Fin (2 * n) // i < p.val i} → Fin r) = r ^ n := by
  rw [Nat.card_fun, Nat.card_fin, AuxBN_strands_card]

theorem AuxBN_labelled_card (n r : ℕ) :
    Nat.card (LabelledBrauerDiagram n r) =
      Nat.card (BrauerPairing n) * r ^ n := by
  unfold LabelledBrauerDiagram
  rw [Nat.card_sigma]
  have h : ∀ p : BrauerPairing n,
      Nat.card ({i : Fin (2 * n) // i < p.val i} → Fin r) = r ^ n :=
    AuxBN_label_card n r
  simp_rw [h]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]

theorem bounded_normal_form_index_count (n r : ℕ) (hr : 0 < r) :
    Nat.card (LabelledBrauerDiagram n r) = r ^ n * oddPairingCount n := by
  rw [AuxBN_labelled_card, AuxBN_pairing_card, mul_comm]

theorem _root_.solution (n r : ℕ) (hr : 0 < r) :
    Nat.card (LabelledBrauerDiagram n r) = r ^ n * oddPairingCount n :=
  bounded_normal_form_index_count n r hr

end QAlgorithms.Papers.Independent.Intake100.P06

end
