-- Prove2me | solution 1 for PolySwap.KMS.proposition_2_24
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T04:23:51.108226+00:00
-- url     : https://prove2.me/submissions/79f9d1bb-6f31-402e-9589-dbc84208dc92

import Mathlib
import Definitions.Def_PolySwap_KMS_Dehn

namespace PolySwap.KMS.Sol224

open PolySwap.KMS Classical

variable {S : Type*}

/-- `l` is a product of conjugates of relators: the data witnessing `Area_R(w) ≤ |l|`. -/
def Valid (R : Set (FreeGroup S)) (w : FreeGroup S) (l : List (FreeGroup S × FreeGroup S)) :
    Prop :=
  (∀ p ∈ l, p.2 ∈ R ∨ p.2⁻¹ ∈ R) ∧ w = (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod

lemma area_le {R : Set (FreeGroup S)} {w : FreeGroup S} {l} (h : Valid R w l) :
    area R w ≤ l.length :=
  iInf_le_of_le l (iInf_le_of_le h le_rfl)

lemma area_attained {R : Set (FreeGroup S)} {w : FreeGroup S} (h : area R w ≠ ⊤) :
    ∃ l, Valid R w l ∧ (l.length : ℕ∞) = area R w := by
  have hne : ∃ l, Valid R w l := by
    by_contra hc
    push Not at hc
    apply h
    simp only [area]
    exact le_antisymm le_top (le_iInf fun l => le_iInf fun hl => absurd hl (hc l))
  have : Nonempty {l // Valid R w l} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  obtain ⟨⟨l, hl⟩, hmin⟩ := csInf_mem (Set.range_nonempty
    (fun l : {l // Valid R w l} => (l.1.length : ℕ∞)))
  refine ⟨l, hl, ?_⟩
  simp only at hmin
  rw [hmin]
  apply le_antisymm
  · exact le_iInf fun l' => le_iInf fun hl' => csInf_le (OrderBot.bddBelow _) ⟨⟨l', hl'⟩, rfl⟩
  · exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨⟨l', hl'⟩, rfl⟩; exact area_le hl')

lemma area_one (R : Set (FreeGroup S)) : area R 1 = 0 :=
  le_antisymm (by simpa using area_le (R := R) (w := 1) (l := []) ⟨by simp, by simp⟩) bot_le

lemma area_mul_le (R : Set (FreeGroup S)) (a b : FreeGroup S) :
    area R (a * b) ≤ area R a + area R b := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  by_cases hb : area R b = ⊤
  · simp [hb]
  obtain ⟨la, ⟨ha1, ha2⟩, hla⟩ := area_attained ha
  obtain ⟨lb, ⟨hb1, hb2⟩, hlb⟩ := area_attained hb
  rw [← hla, ← hlb]
  have := area_le (R := R) (w := a * b) (l := la ++ lb)
    ⟨fun p hp => by
      rcases List.mem_append.1 hp with h | h
      · exact ha1 p h
      · exact hb1 p h,
     by rw [List.map_append, List.prod_append, ← ha2, ← hb2]⟩
  simpa using this

lemma area_conj_le (R : Set (FreeGroup S)) (a u : FreeGroup S) :
    area R (u⁻¹ * a * u) ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      u⁻¹ * (l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod * u =
        ((l.map (fun p => (p.1 * u, p.2))).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons] at ih ⊢
      rw [← ih]; group
  have := area_le (R := R) (w := u⁻¹ * a * u) (l := l.map (fun p => (p.1 * u, p.2)))
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact h1 q hq,
     by rw [h2, key]⟩
  simpa using this

lemma area_inv_le (R : Set (FreeGroup S)) (a : FreeGroup S) : area R a⁻¹ ≤ area R a := by
  by_cases ha : area R a = ⊤
  · simp [ha]
  obtain ⟨l, ⟨h1, h2⟩, hl⟩ := area_attained ha
  rw [← hl]
  have key : ∀ l : List (FreeGroup S × FreeGroup S),
      ((l.map (fun p => p.1⁻¹ * p.2 * p.1)).prod)⁻¹ =
        (((l.map (fun p => (p.1, p.2⁻¹))).reverse).map (fun p => p.1⁻¹ * p.2 * p.1)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append,
        List.prod_append, List.map_nil, List.prod_nil, mul_inv_rev] at ih ⊢
      rw [ih]; group
  have := area_le (R := R) (w := a⁻¹) (l := (l.map (fun p => (p.1, p.2⁻¹))).reverse)
    ⟨fun p hp => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hp)
      rcases h1 q hq with h | h
      · exact Or.inr (by simpa using h)
      · exact Or.inl h,
     by rw [h2, key]⟩
  simpa using this

lemma area_of_mem {R : Set (FreeGroup S)} {ρ : FreeGroup S} (h : ρ ∈ R) : area R ρ ≤ 1 := by
  simpa using area_le (R := R) (w := ρ) (l := [(1, ρ)]) ⟨by simp [h], by simp⟩

/-- The words with a finite area form a normal subgroup containing `R`. -/
def finiteArea (R : Set (FreeGroup S)) : Subgroup (FreeGroup S) where
  carrier := {w | area R w ≠ ⊤}
  one_mem' := by simp [area_one]
  mul_mem' := by
    intro a b ha hb
    exact ne_top_of_le_ne_top (by rw [Ne, ENat.add_eq_top]; exact not_or.2 ⟨ha, hb⟩)
      (area_mul_le R a b)
  inv_mem' := by
    intro a ha
    exact ne_top_of_le_ne_top ha (area_inv_le R a)

instance (R : Set (FreeGroup S)) : (finiteArea R).Normal where
  conj_mem a ha u := by
    have := area_conj_le R a u⁻¹
    rw [inv_inv] at this
    exact ne_top_of_le_ne_top ha this

lemma area_ne_top {R : Set (FreeGroup S)} {w : FreeGroup S} (h : w ∈ Subgroup.normalClosure R) :
    area R w ≠ ⊤ := by
  have : Subgroup.normalClosure R ≤ finiteArea R :=
    Subgroup.normalClosure_le_normal fun ρ hρ =>
      ne_top_of_le_ne_top (by simp) (area_of_mem hρ)
  exact this h

/-- Pushing a product of relator conjugates through a homomorphism. -/
lemma area_map_le {S' : Type*} (R : Set (FreeGroup S)) (R' : Set (FreeGroup S'))
    (ψ : FreeGroup S' →* FreeGroup S) (C : ℕ∞) (hC : ∀ ρ ∈ R', area R (ψ ρ) ≤ C)
    (w : FreeGroup S') (l) (hl : Valid R' w l) : area R (ψ w) ≤ l.length * C := by
  obtain ⟨h1, rfl⟩ := hl
  induction l with
  | nil => simp [area_one]
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, map_inv, List.length_cons]
    have hp : area R (ψ p.2) ≤ C := by
      rcases h1 p (by simp) with h | h
      · exact hC _ h
      · have := area_inv_le R (ψ p.2⁻¹)
        rw [map_inv, inv_inv] at this
        exact this.trans (by rw [← map_inv]; exact hC _ h)
    calc area R ((ψ p.1)⁻¹ * ψ p.2 * ψ p.1 * ψ (List.map (fun p => p.1⁻¹ * p.2 * p.1) l).prod)
        ≤ area R ((ψ p.1)⁻¹ * ψ p.2 * ψ p.1) +
            area R (ψ (List.map (fun p => p.1⁻¹ * p.2 * p.1) l).prod) := area_mul_le _ _ _
      _ ≤ C + l.length * C :=
          add_le_add ((area_conj_le _ _ _).trans hp) (ih fun q hq => h1 q (by simp [hq]))
      _ = ((l.length + 1 : ℕ) : ℕ∞) * C := by push_cast; ring

/-- `|ψ(w)| ≤ C₁ |w|` when every letter maps to a word of length at most `C₁`. -/
lemma norm_lift_le {S' : Type*} (φ : S → FreeGroup S') (C₁ : ℕ)
    (h : ∀ s, wordLength (φ s) ≤ C₁) (w : FreeGroup S) :
    wordLength (FreeGroup.lift φ w) ≤ C₁ * wordLength w := by
  have key : ∀ L : List (S × Bool),
      wordLength (FreeGroup.lift φ (FreeGroup.mk L)) ≤ C₁ * L.length := by
    intro L
    induction L with
    | nil => simp [wordLength]
    | cons x L ih =>
      have hx : FreeGroup.mk (x :: L) = FreeGroup.mk [x] * FreeGroup.mk L := by
        rw [FreeGroup.mul_mk]; rfl
      have h1 : wordLength (FreeGroup.lift φ (FreeGroup.mk [x])) ≤ C₁ := by
        obtain ⟨s, b⟩ := x
        cases b
        · have : FreeGroup.mk [(s, false)] = (FreeGroup.of s)⁻¹ := by
            rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
          rw [this, map_inv, FreeGroup.lift_apply_of]
          simpa [wordLength, FreeGroup.norm_inv_eq] using h s
        · have : FreeGroup.mk [(s, true)] = FreeGroup.of s := rfl
          rw [this, FreeGroup.lift_apply_of]; exact h s
      rw [hx, map_mul]
      calc wordLength (FreeGroup.lift φ (FreeGroup.mk [x]) * FreeGroup.lift φ (FreeGroup.mk L))
          ≤ wordLength (FreeGroup.lift φ (FreeGroup.mk [x])) +
              wordLength (FreeGroup.lift φ (FreeGroup.mk L)) := FreeGroup.norm_mul_le _ _
        _ ≤ C₁ + C₁ * L.length := add_le_add h1 ih
        _ = C₁ * (x :: L).length := by simp; ring
  have := key w.toWord
  rwa [FreeGroup.mk_toWord] at this

/-- `Area_R(w · ψ(w)⁻¹) ≤ C₃ |w|` when every letter satisfies `Area_R(s ψ(s)⁻¹) ≤ C₃`. -/
lemma area_round_trip (R : Set (FreeGroup S)) (ψ : FreeGroup S →* FreeGroup S) (C₃ : ℕ∞)
    (h : ∀ s, area R (FreeGroup.of s * (ψ (FreeGroup.of s))⁻¹) ≤ C₃) (w : FreeGroup S) :
    area R (w * (ψ w)⁻¹) ≤ wordLength w * C₃ := by
  have key : ∀ L : List (S × Bool),
      area R (FreeGroup.mk L * (ψ (FreeGroup.mk L))⁻¹) ≤ L.length * C₃ := by
    intro L
    induction L with
    | nil => simp [← FreeGroup.one_eq_mk, area_one]
    | cons x L ih =>
      have hx : FreeGroup.mk (x :: L) = FreeGroup.mk [x] * FreeGroup.mk L := by
        rw [FreeGroup.mul_mk]; rfl
      set a := FreeGroup.mk [x]
      set y := FreeGroup.mk L
      have ha : area R (a * (ψ a)⁻¹) ≤ C₃ := by
        obtain ⟨s, b⟩ := x
        cases b
        · have : a = (FreeGroup.of s)⁻¹ := by
            simp only [a]; rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
          rw [this]
          have e : (FreeGroup.of s)⁻¹ * (ψ (FreeGroup.of s)⁻¹)⁻¹ =
              (FreeGroup.of s)⁻¹ * (FreeGroup.of s * (ψ (FreeGroup.of s))⁻¹)⁻¹ *
                FreeGroup.of s := by
            rw [map_inv]; group
          rw [e]
          exact (area_conj_le _ _ _).trans ((area_inv_le _ _).trans (h s))
        · exact h s
      rw [hx, map_mul]
      have e : a * y * (ψ a * ψ y)⁻¹ = a⁻¹⁻¹ * (y * (ψ y)⁻¹) * a⁻¹ * (a * (ψ a)⁻¹) := by group
      rw [e]
      calc area R (a⁻¹⁻¹ * (y * (ψ y)⁻¹) * a⁻¹ * (a * (ψ a)⁻¹))
          ≤ area R (a⁻¹⁻¹ * (y * (ψ y)⁻¹) * a⁻¹) + area R (a * (ψ a)⁻¹) := area_mul_le _ _ _
        _ ≤ L.length * C₃ + C₃ := add_le_add ((area_conj_le _ _ _).trans ih) ha
        _ = ((x :: L).length : ℕ∞) * C₃ := by simp; ring
  have := key w.toWord
  rwa [FreeGroup.mk_toWord] at this

end PolySwap.KMS.Sol224

open PolySwap.KMS PolySwap.KMS.Sol224

theorem solution {G : Type*} [Group G] {S S' : Type*} [Finite S] [Finite S']
    (ι : S → G) (R : Set (FreeGroup S)) (ι' : S' → G) (R' : Set (FreeGroup S'))
    (_hP : IsPresentation ι R) (hP' : IsPresentation ι' R') (_hR : R.Finite) (_hR' : R'.Finite)
    (_hS : ∀ s, ∃ t, ι t = (ι s)⁻¹) (_hS' : ∀ s', ∃ t', ι' t' = (ι' s')⁻¹)
    (φ : S → FreeGroup S') (φ' : S' → FreeGroup S)
    (hφ : ∀ s, FreeGroup.lift ι' (φ s) = ι s ∧
      ∀ w, FreeGroup.lift ι' w = ι s → wordLength (φ s) ≤ wordLength w)
    (_hφ' : ∀ s', FreeGroup.lift ι (φ' s') = ι' s' ∧
      ∀ w, FreeGroup.lift ι w = ι' s' → wordLength (φ' s') ≤ wordLength w) :
    ∀ m : ℕ, dehn ι R m ≤
      (⨆ ρ' ∈ R', area R (FreeGroup.lift φ' ρ')) *
          dehn ι' R' ((⨆ s, wordLength (φ s)) * m) +
        (⨆ s, area R (FreeGroup.of s * (FreeGroup.lift φ' (φ s))⁻¹)) * (m : ℕ∞) := by
  intro m
  set C₁ := ⨆ s, wordLength (φ s)
  set C₂ := ⨆ ρ' ∈ R', area R (FreeGroup.lift φ' ρ')
  set C₃ := ⨆ s, area R (FreeGroup.of s * (FreeGroup.lift φ' (φ s))⁻¹)
  have hC₁ : ∀ s, wordLength (φ s) ≤ C₁ := fun s =>
    le_ciSup (f := fun s => wordLength (φ s)) (Set.finite_range _).bddAbove s
  have hcomp : (FreeGroup.lift ι').comp (FreeGroup.lift φ) = FreeGroup.lift ι := by
    ext s; simp [(hφ s).1]
  let ψ := (FreeGroup.lift φ').comp (FreeGroup.lift φ)
  refine iSup₂_le fun w ⟨hw1, hwm⟩ => ?_
  set w' := FreeGroup.lift φ w
  have hw'1 : FreeGroup.lift ι' w' = 1 := by
    rw [← hw1, ← hcomp]; rfl
  have hw'm : wordLength w' ≤ C₁ * m :=
    (norm_lift_le φ C₁ hC₁ w).trans (Nat.mul_le_mul_left _ hwm)
  have hw'ker : w' ∈ Subgroup.normalClosure R' := by
    rw [← hP'.2]; exact hw'1
  obtain ⟨l', hl', hlen⟩ := area_attained (area_ne_top hw'ker)
  have hdehn : area R' w' ≤ dehn ι' R' (C₁ * m) := le_iSup₂_of_le w' ⟨hw'1, hw'm⟩ le_rfl
  have hψ : area R (ψ w) ≤ area R' w' * C₂ := by
    rw [← hlen]
    exact area_map_le R R' (FreeGroup.lift φ') C₂
      (fun ρ hρ => le_iSup₂_of_le (f := fun ρ' (_ : ρ' ∈ R') => area R (FreeGroup.lift φ' ρ'))
        ρ hρ le_rfl) w' l' hl'
  have hrt : area R (w * (ψ w)⁻¹) ≤ wordLength w * C₃ :=
    area_round_trip R ψ C₃ (fun s => le_iSup_of_le s (by simp [ψ])) w
  calc area R w = area R (w * (ψ w)⁻¹ * ψ w) := by rw [inv_mul_cancel_right]
    _ ≤ area R (w * (ψ w)⁻¹) + area R (ψ w) := area_mul_le _ _ _
    _ ≤ (m : ℕ∞) * C₃ + dehn ι' R' (C₁ * m) * C₂ :=
        add_le_add (hrt.trans (mul_le_mul_left (by exact_mod_cast hwm) _))
          (hψ.trans (mul_le_mul_left hdehn _))
    _ = C₂ * dehn ι' R' (C₁ * m) + C₃ * m := by ring
