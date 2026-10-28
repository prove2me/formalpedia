-- Prove2me | solution 1 for PCSPBLPAff.Symmetric.rounding_satisfies
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:40:49.205562+00:00
-- url     : https://prove2.me/submissions/9be90870-e204-4f8c-ac4c-7b39df37914b

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace Aux_PCSP_rs

lemma perm_of_counts {A : Type} [DecidableEq A] {L : ℕ} (u v : Fin L → A)
    (h : ∀ a, (Finset.univ.filter (fun l => u l = a)).card =
      (Finset.univ.filter (fun l => v l = a)).card) :
    ∃ π : Equiv.Perm (Fin L), u ∘ π = v := by
  classical
  have hc : ∀ a, Fintype.card {l // v l = a} = Fintype.card {l // u l = a} := by
    intro a
    rw [Fintype.card_subtype, Fintype.card_subtype, h a]
  let e : ∀ a, {l // v l = a} ≃ {l // u l = a} := fun a => Fintype.equivOfCardEq (hc a)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext l
  exact Equiv.ofFiberEquiv_map e l

end Aux_PCSP_rs

open PCSPBLPAff.Symmetric Aux_PCSP_rs in
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (X : Instance τ ar) {L : ℕ}
    (f : (Fin L → A) → B) (hf : IsPolymorphism 𝔸 𝔹 f) (hfs : IsSymmetric f)
    (W : Fin X.n → A → ℕ) (P : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℕ)
    (hPsupp : ∀ j y, y ∉ 𝔸.rel (X.sym j) → P j y = 0) (hPsum : ∀ j, ∑ y, P j y = L)
    (h9 : ∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
      W (X.scope j k) a =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a), P j y)
    (x : Fin X.n → Fin L → A) (hx : ∀ i, HasCounts (x i) (W i)) :
    ∀ j : Fin X.m, (fun i => f (x i)) ∘ X.scope j ∈ 𝔹.rel (X.sym j) := by
  intro j
  have hcard : Fintype.card (Σ y : Fin (ar (X.sym j)) → A, Fin (P j y)) = L := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hPsum j
  let e : (Σ y : Fin (ar (X.sym j)) → A, Fin (P j y)) ≃ Fin L := Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  let M : Fin L → Fin (ar (X.sym j)) → A := fun l => (e.symm l).1
  have hM : ∀ l, M l ∈ 𝔸.rel (X.sym j) := by
    intro l
    by_contra h
    have h0 := hPsupp j (e.symm l).1 h
    have h1 : ((e.symm l).2 : ℕ) < P j (e.symm l).1 := (e.symm l).2.isLt
    omega
  have hpoly := hf (X.sym j) M hM
  have hcol : ∀ k, f (fun l => M l k) = f (x (X.scope j k)) := by
    intro k
    have hcnt : ∀ a, (Finset.univ.filter (fun l => x (X.scope j k) l = a)).card =
        (Finset.univ.filter (fun l => M l k = a)).card := by
      intro a
      rw [hx (X.scope j k) a, h9 j k a]
      have e1 : (Finset.univ.filter (fun l => M l k = a)).card =
          (Finset.univ.filter (fun q : Σ y : Fin (ar (X.sym j)) → A, Fin (P j y) =>
            q.1 k = a)).card := by
        apply Finset.card_equiv e.symm
        intro l
        simp [M]
      have e2 : (Finset.univ.filter (fun q : Σ y : Fin (ar (X.sym j)) → A, Fin (P j y) =>
            q.1 k = a)) =
          (Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a)).sigma
            (fun _ => Finset.univ) := by
        ext q
        simp [Finset.mem_sigma]
      rw [e1, e2, Finset.card_sigma]
      simp
    obtain ⟨π, hπ⟩ := perm_of_counts _ _ hcnt
    rw [← hπ, hfs]
  have : (fun i => f (x i)) ∘ X.scope j = fun c => f (fun l => M l c) := by
    funext c
    simp only [Function.comp]
    exact (hcol c).symm
  rw [this]
  exact hpoly
