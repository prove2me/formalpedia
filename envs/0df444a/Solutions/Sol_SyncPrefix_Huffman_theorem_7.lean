-- Prove2me | solution 1 for SyncPrefix.Huffman.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T23:05:53.319415+00:00
-- url     : https://prove2.me/submissions/dc7fdb69-b822-42c3-b608-6774e4d05953

import Mathlib
import Definitions.Def_SyncPrefix_Huffman_Constructions

open SyncPrefix.Huffman Computability

section T7

variable {α β : Type} {Z : Language α}

lemma t7_subst_nil (e : β ≃ {z // z ∈ Z}) : subst e [] = [] := rfl

lemma t7_subst_cons (e : β ≃ {z // z ∈ Z}) (b : β) (y : List β) :
    subst e (b :: y) = (e b).val ++ subst e y := rfl

lemma t7_subst_append (e : β ≃ {z // z ∈ Z}) (a b : List β) :
    subst e (a ++ b) = subst e a ++ subst e b := by
  simp [subst]

lemma t7_subst_flatten (e : β ≃ {z // z ∈ Z}) (L : List (List β)) :
    subst e L.flatten = (L.map (subst e)).flatten := by
  induction L with
  | nil => rfl
  | cons y L ih => simp [t7_subst_append, ih]

lemma t7_subst_len_le (e : β ≃ {z // z ∈ Z}) (M : ℕ) (hM : ∀ b, (e b).val.length ≤ M) :
    ∀ y : List β, (subst e y).length ≤ M * y.length := by
  intro y
  induction y with
  | nil => simp [subst]
  | cons b y ih =>
    rw [t7_subst_cons, List.length_append, List.length_cons]
    have := hM b
    nlinarith

lemma t7_subst_len_ge (e : β ≃ {z // z ∈ Z}) (m : ℕ) (hm : ∀ b, m ≤ (e b).val.length) :
    ∀ y : List β, m * y.length ≤ (subst e y).length := by
  intro y
  induction y with
  | nil => simp [subst]
  | cons b y ih =>
    rw [t7_subst_cons, List.length_append, List.length_cons]
    have := hm b
    nlinarith

lemma t7_subst_inj (e : β ≃ {z // z ∈ Z}) (hZ : IsCode Z) (a b : List β)
    (h : subst e a = subst e b) : a = b := by
  have h1 := hZ (a.map fun c => (e c).val) (b.map fun c => (e c).val)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact (e c).2)
    (by intro x hx; simp only [List.mem_map] at hx; obtain ⟨c, _, rfl⟩ := hx; exact (e c).2) h
  have hinj : Function.Injective fun c => (e c).val :=
    fun c d hcd => e.injective (Subtype.ext hcd)
  exact (List.map_injective_iff.2 hinj) h1

lemma t7_Zstar (e : β ≃ {z // z ∈ Z}) (x : List α) (hx : x ∈ Z∗) : ∃ u, x = subst e u := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hx
  clear hx
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons z L ih =>
    obtain ⟨u, hu⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    refine ⟨e.symm ⟨z, hL z (List.mem_cons_self ..)⟩ :: u, ?_⟩
    rw [t7_subst_cons, ← hu]
    simp

lemma t7_star_of_Y (Y : Language β) (e : β ≃ {z // z ∈ Z}) (y : List β) (hy : y ∈ Y∗) :
    subst e y ∈ (compose Y Z e)∗ := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hy
  refine Language.mem_kstar.2 ⟨L.map (subst e), t7_subst_flatten e L, ?_⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hL y hy, rfl⟩

lemma t7_Y_of_star (Y : Language β) (e : β ≃ {z // z ∈ Z}) (x : List α)
    (hx : x ∈ (compose Y Z e)∗) : ∃ y ∈ Y∗, x = subst e y := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.1 hx
  clear hx
  induction L with
  | nil => exact ⟨[], Language.nil_mem_kstar _, rfl⟩
  | cons z L ih =>
    obtain ⟨y, hy, hyL⟩ := ih (fun w hw => hL w (List.mem_cons_of_mem _ hw))
    obtain ⟨y0, hy0, rfl⟩ := hL z (List.mem_cons_self ..)
    refine ⟨y0 ++ y, ?_, ?_⟩
    · obtain ⟨Ly, rfl, hLy⟩ := Language.mem_kstar.1 hy
      refine Language.mem_kstar.2 ⟨y0 :: Ly, by simp, ?_⟩
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hy0
      · exact hLy w hw
    · rw [t7_subst_append, ← hyL]; simp

lemma t7_lift (Y : Language β) (e : β ≃ {z // z ∈ Z}) (hZ : IsCode Z) :
    ∀ xs : List (List α), (∀ x ∈ xs, x ∈ compose Y Z e) →
      ∃ Ly : List (List β), (∀ y ∈ Ly, y ∈ Y) ∧ xs = Ly.map (subst e) := by
  intro xs
  induction xs with
  | nil => intro _; exact ⟨[], by simp, rfl⟩
  | cons x xs ih =>
    intro h
    obtain ⟨Ly, hLy, rfl⟩ := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    obtain ⟨y, hy, rfl⟩ := h x (List.mem_cons_self ..)
    refine ⟨y :: Ly, ?_, rfl⟩
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hy
    · exact hLy w hw

end T7

theorem solution {α β : Type} (Y : Language β) (Z : Language α)
    (hY : IsSyncCode Y) (hZ : IsSyncCode Z) (hZfin : Set.Finite (Z : Set (List α)))
    (e : β ≃ {z // z ∈ Z}) (m M : ℕ)
    (hm : IsLeast ((fun z : List α => z.length) '' (Z : Set (List α))) m)
    (hM : IsGreatest ((fun z : List α => z.length) '' (Z : Set (List α))) M) :
    IsSyncCode (compose Y Z e) ∧ m * absorbLength Y ≤ absorbLength (compose Y Z e) ∧
      absorbLength (compose Y Z e) ≤ 2 * M * absorbLength Y + 2 * absorbLength Z := by
  obtain ⟨⟨hYcode, hYcomp⟩, lY0, rY0, hYabs0⟩ := hY
  obtain ⟨⟨hZcode, hZcomp⟩, lZ0, rZ0, hZabs0⟩ := hZ
  have hmb : ∀ b, m ≤ (e b).val.length := fun b => hm.2 ⟨(e b).val, (e b).2, rfl⟩
  have hMb : ∀ b, (e b).val.length ≤ M := fun b => hM.2 ⟨(e b).val, (e b).2, rfl⟩
  set X := compose Y Z e with hXdef
  -- shortest absorbing pairs
  obtain ⟨lY, rY, hYabs, hYlen⟩ : ∃ l r, IsAbsorbing Y l r ∧ l.length + r.length = absorbLength Y :=
    Nat.sInf_mem (s := {L | ∃ l r, IsAbsorbing Y l r ∧ l.length + r.length = L})
      ⟨_, lY0, rY0, hYabs0, rfl⟩
  obtain ⟨lZ, rZ, hZabs, hZlen⟩ : ∃ l r, IsAbsorbing Z l r ∧ l.length + r.length = absorbLength Z :=
    Nat.sInf_mem (s := {L | ∃ l r, IsAbsorbing Z l r ∧ l.length + r.length = L})
      ⟨_, lZ0, rZ0, hZabs0, rfl⟩
  obtain ⟨u, hu⟩ := t7_Zstar e lZ hZabs.1
  obtain ⟨v, hv⟩ := t7_Zstar e rZ hZabs.2.1
  -- the absorbing pair of `X`
  set A := subst e lY
  set B := subst e rY
  have hYu : lY ++ u ++ rY ∈ Y∗ :=
    hYabs.2.2 _ ⟨u ++ rY, by simp⟩ ⟨lY ++ u, rfl⟩
  have hYv : lY ++ v ++ rY ∈ Y∗ :=
    hYabs.2.2 _ ⟨v ++ rY, by simp⟩ ⟨lY ++ v, rfl⟩
  have hlX : subst e (lY ++ u ++ rY) = A ++ lZ ++ B := by
    rw [t7_subst_append, t7_subst_append, ← hu]
  have hrX : subst e (lY ++ v ++ rY) = A ++ rZ ++ B := by
    rw [t7_subst_append, t7_subst_append, ← hv]
  have hXabs : IsAbsorbing X (A ++ lZ ++ B) (A ++ rZ ++ B) := by
    refine ⟨hlX ▸ t7_star_of_Y Y e _ hYu, hrX ▸ t7_star_of_Y Y e _ hYv, ?_⟩
    intro w hlw hrw
    obtain ⟨t, rfl⟩ := hlw
    set w := A ++ lZ ++ B ++ t with hw
    set s := lZ ++ B ++ t with hs
    have hws : w = A ++ s := by simp [hw, hs]
    have hsuf1 : s <:+ w := ⟨A, hws.symm⟩
    have hsuf2 : rZ ++ B <:+ w := (List.suffix_append A (rZ ++ B)).trans
      (by simpa [List.append_assoc] using hrw)
    have hlenw := hrw.length_le
    have hsl : (rZ ++ B).length ≤ s.length := by
      simp only [hws, List.length_append] at hlenw ⊢
      omega
    obtain ⟨s0, hs0⟩ := List.suffix_of_suffix_length_le hsuf2 hsuf1 hsl
    set w2 := s0 ++ rZ with hw2
    have hs2 : s = w2 ++ B := by rw [← hs0]; simp [hw2]
    have hpre1 : lZ <+: s := ⟨B ++ t, by simp [hs]⟩
    have hpre2 : w2 <+: s := ⟨B, hs2.symm⟩
    have hlen2 : lZ.length ≤ w2.length := by
      have h1 : s.length = lZ.length + B.length + t.length := by simp [hs]; omega
      have h2 : s.length = w2.length + B.length := by rw [hs2]; simp
      omega
    have hw2Z : w2 ∈ Z∗ :=
      hZabs.2.2 w2 (List.prefix_of_prefix_length_le hpre1 hpre2 hlen2) ⟨s0, rfl⟩
    obtain ⟨y2, hy2⟩ := t7_Zstar e w2 hw2Z
    have hy : lY ++ y2 ++ rY ∈ Y∗ :=
      hYabs.2.2 _ ⟨y2 ++ rY, by simp⟩ ⟨lY ++ y2, rfl⟩
    have := t7_star_of_Y Y e _ hy
    rw [t7_subst_append, t7_subst_append, ← hy2] at this
    rw [hws, hs2]
    simpa [List.append_assoc] using this
  refine ⟨⟨⟨?_, ?_⟩, _, _, hXabs⟩, ?_, ?_⟩
  · -- `X` is a code
    intro xs ys hxs hys hflat
    obtain ⟨Lx, hLx, rfl⟩ := t7_lift Y e hZcode xs hxs
    obtain ⟨Ly, hLy, rfl⟩ := t7_lift Y e hZcode ys hys
    rw [← t7_subst_flatten, ← t7_subst_flatten] at hflat
    have := hYcode Lx Ly hLx hLy (t7_subst_inj e hZcode _ _ hflat)
    rw [this]
  · -- completeness
    intro w
    obtain ⟨v1, v2, hv12⟩ := hZcomp w
    obtain ⟨y, hy⟩ := t7_Zstar e _ hv12
    obtain ⟨y1, y2, hy12⟩ := hYcomp y
    refine ⟨subst e y1 ++ v1, v2 ++ subst e y2, ?_⟩
    have := t7_star_of_Y Y e _ hy12
    rw [t7_subst_append, t7_subst_append, ← hy] at this
    simpa [List.append_assoc] using this
  · -- lower bound
    obtain ⟨l, r, hXabs', hXlen⟩ : ∃ l r, IsAbsorbing X l r ∧ l.length + r.length = absorbLength X :=
      Nat.sInf_mem (s := {L | ∃ l r, IsAbsorbing X l r ∧ l.length + r.length = L})
        ⟨_, _, _, hXabs, rfl⟩
    obtain ⟨l', hl'Y, rfl⟩ := t7_Y_of_star Y e l hXabs'.1
    obtain ⟨r', hr'Y, rfl⟩ := t7_Y_of_star Y e r hXabs'.2.1
    have habs : IsAbsorbing Y l' r' := by
      refine ⟨hl'Y, hr'Y, ?_⟩
      intro w' hl hr
      obtain ⟨t, rfl⟩ := hl
      obtain ⟨t', ht'⟩ := hr
      have h1 : subst e (l' ++ t) ∈ X∗ := by
        apply hXabs'.2.2
        · exact ⟨subst e t, by rw [t7_subst_append]⟩
        · exact ⟨subst e t', by rw [← ht', t7_subst_append]⟩
      obtain ⟨y, hy, hyeq⟩ := t7_Y_of_star Y e _ h1
      rw [t7_subst_inj e hZcode _ _ hyeq]
      exact hy
    have h1 : absorbLength Y ≤ l'.length + r'.length := Nat.sInf_le ⟨_, _, habs, rfl⟩
    have h2 := t7_subst_len_ge e m hmb l'
    have h3 := t7_subst_len_ge e m hmb r'
    rw [← hXlen]
    calc m * absorbLength Y ≤ m * (l'.length + r'.length) := Nat.mul_le_mul_left _ h1
      _ = m * l'.length + m * r'.length := by ring
      _ ≤ _ := by omega
  · -- upper bound
    have h1 : absorbLength X ≤ (A ++ lZ ++ B).length + (A ++ rZ ++ B).length :=
      Nat.sInf_le ⟨_, _, hXabs, rfl⟩
    have hA := t7_subst_len_le e M hMb lY
    have hB := t7_subst_len_le e M hMb rY
    simp only [List.length_append] at h1
    rw [← hYlen, ← hZlen]
    have : M * lY.length + M * rY.length = M * (lY.length + rY.length) := by ring
    nlinarith
