-- Prove2me | solution 1 for PCB.automorphism_invariant
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:33:45.845262+00:00
-- url     : https://prove2.me/submissions/660165b6-68cb-45ac-892c-4c374076c50f

import Mathlib
import Definitions.Def_PCB_alg
import Definitions.Def_PCB_tor

namespace PCB88

def hz (a : ℤ) : ℤ := if 0 ≤ a then a + 1 else a
def hinv (z : ℤ) : ℤ := if 0 < z then z - 1 else z

lemma hz_ne (a : ℤ) : hz a ≠ 0 := by unfold hz; split_ifs <;> omega
lemma hinv_hz (a : ℤ) : hinv (hz a) = a := by unfold hz hinv; split_ifs <;> omega
lemma hz_hinv {z : ℤ} (hz0 : z ≠ 0) : hz (hinv z) = z := by unfold hz hinv; split_ifs <;> omega

def nfZ (p : ℤ × ℤ) : ℤ × ℤ :=
  if p.2 = 0 then (if p.1 % 2 = 0 then (p.1 / 2, 0) else (0, hz (p.1 / 2)))
  else (hz p.1, if p.1 = 1 then -p.2 else p.2)

def invZ (q : ℤ × ℤ) : ℤ × ℤ :=
  if q.2 = 0 then (2 * q.1, 0)
  else if q.1 = 0 then (2 * hinv q.2 + 1, 0)
  else (hinv q.1, if hinv q.1 = 1 then -q.2 else q.2)

lemma invZ_nfZ (p : ℤ × ℤ) : invZ (nfZ p) = p := by
  obtain ⟨a, b⟩ := p
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a % 2 = 0
    · simp only [nfZ, invZ, ha, if_true]; ext <;> simp <;> omega
    · have h1 := hz_ne (a / 2)
      simp only [nfZ, invZ, ha, if_true, if_false, h1, hinv_hz]
      ext <;> simp <;> omega
  · have h1 := hz_ne a
    by_cases ha : a = 1
    · subst ha; simp [nfZ, invZ, hb, h1, hinv_hz]
    · simp [nfZ, invZ, hb, h1, hinv_hz, ha]

lemma nfZ_invZ (q : ℤ × ℤ) : nfZ (invZ q) = q := by
  obtain ⟨x, y⟩ := q
  by_cases hy : y = 0
  · subst hy; simp [nfZ, invZ]
  · by_cases hx : x = 0
    · subst hx
      have : (2 * hinv y + 1) % 2 ≠ 0 := by omega
      have e : (2 * hinv y + 1) / 2 = hinv y := by omega
      simp [nfZ, invZ, hy, this, e, hz_hinv hy]
    · have hx' := hz_hinv hx
      by_cases h1 : hinv x = 1
      · have e1 : invZ (x, y) = (1, -y) := by simp [invZ, hy, hx, h1]
        have e2 : hz 1 = x := by rw [← h1, hx']
        rw [e1]; simp [nfZ, hy, e2]
      · simp [nfZ, invZ, hy, hx, h1, hx']

lemma invZ_snd (q : ℤ × ℤ) (h : q.1 = 0 ∨ q.2 = 0) : (invZ q).2 = 0 := by
  unfold invZ; split_ifs with h1 h2 <;> simp_all

abbrev G := Multiplicative (ℤ × ℤ)
abbrev FF : Fin 2 → Type := fun _ => Multiplicative ℤ

def nfG (g : G) : ∀ j : Fin 2, FF j :=
  fun j => if j = 0 then Multiplicative.ofAdd (nfZ g.toAdd).1 else Multiplicative.ofAdd (nfZ g.toAdd).2

def asm (x : ∀ j : Fin 2, FF j) : G :=
  Multiplicative.ofAdd (invZ ((x 0).toAdd, (x 1).toAdd))

def pos : Set (Multiplicative ℤ) := {x | 0 < x.toAdd}

lemma pos_cone : PCB.IsPositiveCone pos := by
  refine ⟨by simp [pos], fun a ha b hb => ?_, fun a ha h => ?_, fun g hg => ?_, fun a ha g => ?_⟩
  · simp only [pos, Set.mem_ofPred_eq, toAdd_mul] at *; omega
  · simp only [pos, Set.mem_ofPred_eq, toAdd_inv] at *; omega
  · simp only [pos, Set.mem_ofPred_eq, toAdd_inv]
    have : g.toAdd ≠ 0 := fun h => hg (by simpa using congrArg Multiplicative.ofAdd h)
    omega
  · rw [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one]; exact ha

def S : Subgroup G where
  carrier := {g | g.toAdd.2 = 0 ∧ g.toAdd.1 % 2 = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, toAdd_mul, Prod.fst_add, Prod.snd_add] at *; omega
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, toAdd_inv, Prod.fst_neg, Prod.snd_neg] at *; omega

lemma nfZ_snd_eq_zero (p : ℤ × ℤ) : (nfZ p).2 = 0 ↔ p.2 = 0 ∧ p.1 % 2 = 0 := by
  unfold nfZ
  split_ifs with h1 h2 h3
  · simp [h1, h2]
  · simp [h1, h2, hz_ne]
  · simp [h1]
  · simp [h1]

noncomputable def W : PCB.AlmostDirectProductWorld 2 G FF where
  cone := fun _ => pos
  conePos := fun _ => pos_cone
  nf := nfG
  assemble := asm
  assemble_nf := by
    intro g
    simp only [asm, nfG]
    simp [invZ_nfZ]
  nf_assemble := by
    intro x
    funext j
    fin_cases j
    · simp [asm, nfG, nfZ_invZ]
    · simp [asm, nfG, nfZ_invZ]
  conjOn := fun _ _ f => f
  conjOn_cone := fun _ _ _ h => h
  nf_conj := by
    intro x g j
    rw [mul_comm x g, mul_inv_cancel_right]
  tower := fun j => if j = 0 then S else ⊤
  towerMem := by
    intro j g
    fin_cases j
    · simp only [Fin.zero_eta, if_true]
      constructor
      · intro hg i hi
        have : i = 1 := by omega
        subst this
        have := (nfZ_snd_eq_zero g.toAdd).2 hg
        simp [nfG, this]
      · intro h
        have h1 := h 1 (by decide)
        simp only [nfG] at h1
        have h2 : (nfZ g.toAdd).2 = 0 := by simpa using h1
        exact (nfZ_snd_eq_zero _).1 h2
    · simp only [Fin.mk_one, if_neg (by decide : (1 : Fin 2) ≠ 0), Subgroup.mem_top, true_iff]
      intro i hi; exact absurd hi (by omega)

def φ : G ≃* G where
  toFun g := Multiplicative.ofAdd (g.toAdd.1 + g.toAdd.2, g.toAdd.2)
  invFun g := Multiplicative.ofAdd (g.toAdd.1 - g.toAdd.2, g.toAdd.2)
  left_inv g := by simp
  right_inv g := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
    ext <;> simp <;> ring

lemma φ_fix {g : G} (h : g.toAdd.2 = 0) : φ g = g := by
  apply Multiplicative.toAdd.injective
  simp only [φ, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd, h, add_zero]
  rw [← h]

lemma φsymm_fix {g : G} (h : g.toAdd.2 = 0) : φ.symm g = g := by
  rw [MulEquiv.symm_apply_eq, φ_fix h]

lemma embed_snd (j : Fin 2) (f : FF j) : (PCB.embedFactor W j f).toAdd.2 = 0 := by
  simp only [PCB.embedFactor, W, asm, toAdd_ofAdd]
  apply invZ_snd
  fin_cases j
  · right; simp
  · left; simp

lemma hyp (j : Fin 2) (f : FF j) (hf : f ∈ W.cone j) : ∃ f' ∈ W.cone j,
    ∀ i : Fin 2, W.nf (φ (PCB.embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1 := by
  refine ⟨f, hf, fun i => ?_⟩
  rw [φ_fix (embed_snd j f)]
  simp only [PCB.embedFactor]
  rw [W.nf_assemble]

lemma hypInv (j : Fin 2) (f : FF j) (hf : f ∈ W.cone j) : ∃ f' ∈ W.cone j,
    ∀ i : Fin 2, W.nf (φ.symm (PCB.embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1 := by
  refine ⟨f, hf, fun i => ?_⟩
  rw [φsymm_fix (embed_snd j f)]
  simp only [PCB.embedFactor]
  rw [W.nf_assemble]

def g0 : G := Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ))

lemma g0_mem : g0 ∈ PCB.lexCone W := by
  refine ⟨1, fun i hi => absurd hi (by omega), ?_⟩
  simp [W, nfG, g0, nfZ, pos, hz]

lemma φg0_not_mem : φ g0 ∉ PCB.lexCone W := by
  rintro ⟨j, hj, hc⟩
  have e : φ g0 = Multiplicative.ofAdd ((1 : ℤ), (1 : ℤ)) := by
    apply Multiplicative.toAdd.injective; simp [φ, g0]
  rw [e] at hj hc
  fin_cases j
  · have := hj 1 (by decide)
    simp [W, nfG, nfZ] at this
  · simp [W, nfG, nfZ, pos] at hc

end PCB88

open PCB in
theorem solution : ¬ (∀ {k : ℕ} {G : Type} [Group G] {F : Fin k → Type} [∀ j, Group (F j)]
    (W : AlmostDirectProductWorld k G F) (φ : G ≃* G)
    (h : ∀ (j : Fin k) (f : F j), f ∈ W.cone j → ∃ f' ∈ W.cone j,
      ∀ i : Fin k, W.nf (φ (embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1)
    (hInv : ∀ (j : Fin k) (f : F j), f ∈ W.cone j → ∃ f' ∈ W.cone j,
      ∀ i : Fin k, W.nf (φ.symm (embedFactor W j f)) i = if h2 : i = j then h2 ▸ f' else 1),
    (∀ g, g ∈ lexCone W → φ g ∈ lexCone W) ∧
    (∀ g, g ∈ lexCone W → φ.symm g ∈ lexCone W)) := by
  intro H
  exact PCB88.φg0_not_mem ((H PCB88.W PCB88.φ PCB88.hyp PCB88.hypInv).1 _ PCB88.g0_mem)
