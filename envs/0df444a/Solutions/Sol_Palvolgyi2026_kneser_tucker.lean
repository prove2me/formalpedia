-- Prove2me | solution 1 for Palvolgyi2026.kneser_tucker
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:43:51.429768+00:00
-- url     : https://prove2.me/submissions/568deb3f-c88e-4726-8446-a5fc07d19269
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Ziegler2002_zp_tucker

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical
/-! Blueprint: Pálvölgyi's Kneser-shift theorem (Palvolgyi2026.kneser_shift) from Ziegler's
Z_p-Tucker lemma (Ziegler2002.zp_tucker), following Section 4 of arXiv:2608.10865. -/
/-- `𝒜 ∈ P_p(n,k)`: families of `k`-subsets of `[n]`, members of different coordinates disjoint,
not all families empty. -/
def InP {q n : ℕ} (k : ℕ) (𝒜 : Fin (q + 1) → Finset (Finset (Fin n))) : Prop :=
  (∀ i, ∀ A ∈ 𝒜 i, A.card = k) ∧
  (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) ∧
  ∃ i, (𝒜 i).Nonempty

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS.PartT
open RamseyDisambig.Dev.KS Classical
variable {q n : ℕ}
/-- Pairwise disjoint coordinates. -/
def PD (X : Fin (q + 1) → Finset (Fin n)) : Prop := ∀ i j, i ≠ j → Disjoint (X i) (X j)

def High (k : ℕ) (X : Fin (q + 1) → Finset (Fin n)) : Prop := ∃ i, k ≤ (X i).card

def AA (k : ℕ) (X : Fin (q + 1) → Finset (Fin n)) : Fin (q + 1) → Finset (Finset (Fin n)) :=
  fun i => (X i).powersetCard k

def IsMinCoord (X : Fin (q + 1) → Finset (Fin n)) (i : Fin (q + 1)) : Prop :=
  ∃ a ∈ X i, ∀ j, ∀ b ∈ X j, a ≤ b

noncomputable def coord (X : Fin (q + 1) → Finset (Fin n)) : Fin (q + 1) :=
  if h : ∃ i, IsMinCoord X i then Classical.choose h else 0

noncomputable def ell (k m : ℕ) (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (X : Fin (q + 1) → Finset (Fin n)) : ℕ :=
  if High k X then (q + 1) * (k - 1) + ((μ (AA k X)).2.val + 1) else ∑ i, (X i).card

noncomputable def sgn (k m : ℕ) (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (X : Fin (q + 1) → Finset (Fin n)) : Fin (q + 1) :=
  if High k X then (μ (AA k X)).1 else coord X

noncomputable def lamF (k m M : ℕ)
    (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (X : Fin (q + 1) → Finset (Fin n)) : Fin (q + 1) × Fin (M + 1) :=
  (sgn k m μ X, ⟨((ell k m μ X - 1) / q) % (M + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)

lemma coord_unique {X : Fin (q + 1) → Finset (Fin n)} (hD : PD X) {i i' : Fin (q + 1)}
    (h : IsMinCoord X i) (h' : IsMinCoord X i') : i = i' := by
  obtain ⟨a, ha, hamin⟩ := h
  obtain ⟨a', ha', hamin'⟩ := h'
  have : a = a' := le_antisymm (hamin _ _ ha') (hamin' _ _ ha)
  subst this
  by_contra hne
  exact Finset.disjoint_left.mp (hD i i' hne) ha ha'

lemma coord_spec {X : Fin (q + 1) → Finset (Fin n)} (hD : PD X) {i : Fin (q + 1)}
    (h : IsMinCoord X i) : coord X = i := by
  have he : ∃ i, IsMinCoord X i := ⟨i, h⟩
  unfold coord
  rw [dif_pos he]
  exact coord_unique hD (Classical.choose_spec he) h

lemma exists_min {X : Fin (q + 1) → Finset (Fin n)} (hne : ∃ i, (X i).Nonempty) :
    ∃ i, IsMinCoord X i := by
  have hU : (Finset.univ.biUnion X).Nonempty := by
    obtain ⟨i, x, hx⟩ := hne
    exact ⟨x, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩⟩
  have hmem := Finset.min'_mem _ hU
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hmem
  refine ⟨i, _, hi, fun j b hb => ?_⟩
  exact Finset.min'_le _ _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hb⟩)

lemma isMin_shift {X : Fin (q + 1) → Finset (Fin n)} {i : Fin (q + 1)} (h : IsMinCoord X i) :
    IsMinCoord (fun j => X (j - 1)) (i + 1) := by
  obtain ⟨a, ha, hamin⟩ := h
  refine ⟨a, by simpa using ha, fun j b hb => hamin (j - 1) b hb⟩

lemma PD_shift {X : Fin (q + 1) → Finset (Fin n)} (hD : PD X) : PD (fun j => X (j - 1)) := by
  intro i j hij
  exact hD _ _ (fun h => hij (sub_left_inj.mp h))

lemma high_shift (k : ℕ) (X : Fin (q + 1) → Finset (Fin n)) :
    High k (fun j => X (j - 1)) ↔ High k X := by
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i - 1, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i + 1, by simpa using hi⟩

lemma sum_shift (X : Fin (q + 1) → Finset (Fin n)) :
    ∑ i, (X (i - 1)).card = ∑ i, (X i).card :=
  Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)

lemma InP_AA (k : ℕ) {X : Fin (q + 1) → Finset (Fin n)} (hD : PD X) (hH : High k X) :
    InP k (AA k X) := by
  refine ⟨fun i A hA => (Finset.mem_powersetCard.mp hA).2, ?_, ?_⟩
  · intro i j hij A hA B hB
    exact Finset.disjoint_of_subset_left (Finset.mem_powersetCard.mp hA).1
      (Finset.disjoint_of_subset_right (Finset.mem_powersetCard.mp hB).1 (hD i j hij))
  · obtain ⟨i, hi⟩ := hH
    exact ⟨i, Finset.powersetCard_nonempty.mpr hi⟩

lemma low_sum_le (k : ℕ) {X : Fin (q + 1) → Finset (Fin n)} (hH : ¬ High k X) :
    ∑ i, (X i).card ≤ (q + 1) * (k - 1) := by
  have : ∀ i ∈ (Finset.univ : Finset (Fin (q + 1))), (X i).card ≤ k - 1 := by
    intro i _
    have : ¬ k ≤ (X i).card := fun h => hH ⟨i, h⟩
    omega
  calc ∑ i, (X i).card ≤ ∑ _i : Fin (q + 1), (k - 1) := Finset.sum_le_sum this
    _ = (q + 1) * (k - 1) := by simp

lemma ell_bounds (k m : ℕ) (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    {X : Fin (q + 1) → Finset (Fin n)} (hne : ∃ i, (X i).Nonempty) :
    1 ≤ ell k m μ X ∧ ell k m μ X ≤ (q + 1) * (k - 1) + m := by
  unfold ell
  split_ifs with hH
  · have := (μ (AA k X)).2.isLt
    omega
  · refine ⟨?_, (low_sum_le k hH).trans (Nat.le_add_right _ _)⟩
    obtain ⟨i, hi⟩ := hne
    calc 1 ≤ (X i).card := Finset.card_pos.mpr hi
      _ ≤ ∑ j, (X j).card :=
        Finset.single_le_sum (f := fun j => (X j).card) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)

lemma key (k m : ℕ) (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (htie : ∀ 𝒜 ℬ, InP k 𝒜 → InP k ℬ → 𝒜 ≤ ℬ → (μ 𝒜).2 = (μ ℬ).2 → (μ 𝒜).1 = (μ ℬ).1)
    {X Y : Fin (q + 1) → Finset (Fin n)} (hDX : PD X) (hDY : PD Y) (hXY : X < Y)
    (hs : sgn k m μ X ≠ sgn k m μ Y) : ell k m μ X ≠ ell k m μ Y := by
  obtain ⟨hle, i, hi⟩ := Pi.lt_def.mp hXY
  by_cases hX : High k X <;> by_cases hY : High k Y
  · intro heq
    unfold ell at heq
    rw [if_pos hX, if_pos hY] at heq
    have h2 : (μ (AA k X)).2 = (μ (AA k Y)).2 := Fin.ext (by omega)
    apply hs
    unfold sgn
    rw [if_pos hX, if_pos hY]
    exact htie _ _ (InP_AA k hDX hX) (InP_AA k hDY hY)
      (fun j => Finset.powersetCard_mono (hle j)) h2
  · exfalso
    obtain ⟨j, hj⟩ := hX
    exact hY ⟨j, hj.trans (Finset.card_le_card (hle j))⟩
  · unfold ell
    rw [if_neg hX, if_pos hY]
    have := low_sum_le k hX
    omega
  · unfold ell
    rw [if_neg hX, if_neg hY]
    apply Nat.ne_of_lt
    exact Finset.sum_lt_sum (fun j _ => Finset.card_le_card (hle j))
      ⟨i, Finset.mem_univ _, Finset.card_lt_card hi⟩

theorem kneser_tucker (q : ℕ) (hp : (q + 1).Prime) (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hnk : (q + 1) * k + m ≤ n + 1)
    (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (hμ : ∀ 𝒜, InP k 𝒜 → μ (fun i => 𝒜 (i - 1)) = ((μ 𝒜).1 + 1, (μ 𝒜).2))
    (htie : ∀ 𝒜 ℬ, InP k 𝒜 → InP k ℬ → 𝒜 ≤ ℬ → (μ 𝒜).2 = (μ ℬ).2 → (μ 𝒜).1 = (μ ℬ).1) :
    False := by
  have hq : 0 < q := by have := hp.two_le; omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = ((q + 1) * (k - 1) + m - 1) / q := ⟨_, rfl⟩
  have hkey : (q + 1) * (k - 1) + m - 1 + q ≤ n - 1 := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have : (q + 1) * (k' + 1) = (q + 1) * k' + q + 1 := by ring
    simp only [Nat.add_sub_cancel]
    omega
  have hMn : M + 1 ≤ (n - 1) / q := by
    rw [Nat.le_div_iff_mul_le hq, Nat.add_mul, one_mul]
    have : M * q ≤ (q + 1) * (k - 1) + m - 1 := hMdef ▸ Nat.div_mul_le_self _ _
    omega
  have hn : 1 ≤ n := by
    have : (q + 1) * 1 ≤ (q + 1) * k := Nat.mul_le_mul_left _ hk
    omega
  have hlam : ∀ X : Fin (q + 1) → Finset (Fin n),
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) → (∃ i, (X i).Nonempty) →
        lamF k m M μ (fun i => X (i - 1)) =
          ((lamF k m M μ X).1 + 1, (lamF k m M μ X).2) := by
    intro X hD hne
    have hD' : PD X := hD
    have hAA : AA k (fun i => X (i - 1)) = fun i => AA k X (i - 1) := rfl
    by_cases hH : High k X
    · have hH' : High k (fun i => X (i - 1)) := (high_shift k X).mpr hH
      have hμX := hμ (AA k X) (InP_AA k hD' hH)
      have hs : sgn k m μ (fun i => X (i - 1)) = sgn k m μ X + 1 := by
        unfold sgn; rw [if_pos hH, if_pos hH', hAA, hμX]
      have he : ell k m μ (fun i => X (i - 1)) = ell k m μ X := by
        unfold ell; rw [if_pos hH, if_pos hH', hAA, hμX]
      simp only [lamF, hs, he]
    · have hH' : ¬ High k (fun i => X (i - 1)) := fun h => hH ((high_shift k X).mp h)
      obtain ⟨i, hi⟩ := exists_min hne
      have hs : sgn k m μ (fun i => X (i - 1)) = sgn k m μ X + 1 := by
        unfold sgn; rw [if_neg hH, if_neg hH', coord_spec hD' hi,
          coord_spec (PD_shift hD') (isMin_shift hi)]
      have he : ell k m μ (fun i => X (i - 1)) = ell k m μ X := by
        unfold ell; rw [if_neg hH, if_neg hH', sum_shift]
      simp only [lamF, hs, he]
  obtain ⟨Y, hY, hmono, h2, hinj⟩ :=
    Ziegler2002.zp_tucker q hp n (M + 1) hn (Nat.succ_pos _) hMn (lamF k m M μ) hlam
  have hLinj : Function.Injective (fun j => ell k m μ (Y j)) := by
    intro j j' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key k m μ htie (hY j).1 (hY j').1 (hmono hlt)
        (fun he => hne (hinj he)) h
    · exact key k m μ htie (hY j').1 (hY j).1 (hmono hlt)
        (fun he => hne (hinj he).symm) h.symm
  have hb := fun j => ell_bounds k m μ (hY j).2
  have hdiv : ∀ j, (ell k m μ (Y j) - 1) / q = (ell k m μ (Y 0) - 1) / q := by
    intro j
    have h20 := congrArg Fin.val (h2 j 0)
    simp only [lamF] at h20
    have hlt : ∀ j, (ell k m μ (Y j) - 1) / q < M + 1 := by
      intro j
      have : (ell k m μ (Y j) - 1) / q ≤ M := by
        rw [hMdef]; exact Nat.div_le_div_right (by have := (hb j).2; omega)
      omega
    rwa [Nat.mod_eq_of_lt (hlt j), Nat.mod_eq_of_lt (hlt 0)] at h20
  let f : Fin (q + 1) → Fin q := fun j => ⟨(ell k m μ (Y j) - 1) % q, Nat.mod_lt _ hq⟩
  have hf : Function.Injective f := by
    intro j j' h
    have hm' : (ell k m μ (Y j) - 1) % q = (ell k m μ (Y j') - 1) % q := congrArg Fin.val h
    apply hLinj
    show ell k m μ (Y j) = ell k m μ (Y j')
    have e1 := Nat.div_add_mod (ell k m μ (Y j) - 1) q
    have e2 := Nat.div_add_mod (ell k m μ (Y j') - 1) q
    rw [hdiv j] at e1
    rw [hdiv j'] at e2
    have := (hb j).1
    have := (hb j').1
    omega
  have := Fintype.card_le_of_injective f hf
  simp at this

end RamseyDisambig.Dev.KS.PartT
end

section
set_option autoImplicit false
namespace RamseyDisambig.Dev.KS
open Classical
alias kneser_tucker := RamseyDisambig.Dev.KS.PartT.kneser_tucker

end RamseyDisambig.Dev.KS
end

section
set_option autoImplicit false
namespace Palvolgyi2026

theorem chk_kneser_tucker (q : ℕ) (hp : (q + 1).Prime) (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (hnk : m - 1 ≤ n - (q + 1) * k) (hpk : (q + 1) * k ≤ n)
    (μ : (Fin (q + 1) → Finset (Finset (Fin n))) → Fin (q + 1) × Fin m)
    (hμ : ∀ 𝒜 : Fin (q + 1) → Finset (Finset (Fin n)),
      (∀ i, ∀ A ∈ 𝒜 i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) →
      (∃ i, (𝒜 i).Nonempty) →
        μ (fun i => 𝒜 (i - 1)) = ((μ 𝒜).1 + 1, (μ 𝒜).2))
    (htie : ∀ 𝒜 ℬ : Fin (q + 1) → Finset (Finset (Fin n)),
      (∀ i, ∀ A ∈ 𝒜 i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ 𝒜 i, ∀ B ∈ 𝒜 j, Disjoint A B) →
      (∃ i, (𝒜 i).Nonempty) →
      (∀ i, ∀ A ∈ ℬ i, A.card = k) → (∀ i j, i ≠ j → ∀ A ∈ ℬ i, ∀ B ∈ ℬ j, Disjoint A B) →
      (∃ i, (ℬ i).Nonempty) →
      𝒜 ≤ ℬ → (μ 𝒜).2 = (μ ℬ).2 → (μ 𝒜).1 = (μ ℬ).1) :
    False :=
  RamseyDisambig.Dev.KS.kneser_tucker q hp n k m hk hm (by omega) μ
    (fun 𝒜 h => hμ 𝒜 h.1 h.2.1 h.2.2)
    (fun 𝒜 ℬ h1 h2 => htie 𝒜 ℬ h1.1 h1.2.1 h1.2.2 h2.1 h2.2.1 h2.2.2)

end Palvolgyi2026
end

theorem solution : type_of% @Palvolgyi2026.chk_kneser_tucker := @Palvolgyi2026.chk_kneser_tucker
