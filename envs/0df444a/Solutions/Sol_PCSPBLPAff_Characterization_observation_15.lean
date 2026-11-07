-- Prove2me | solution 1 for PCSPBLPAff.Characterization.observation_15
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T10:06:47.241615+00:00
-- url     : https://prove2.me/submissions/02a96c08-6380-4ff8-ac0a-3843397d0d63

import Mathlib
import Definitions.Def_PCSPBLPAff_Characterization_Setting

open PCSPBLPAff.Symmetric PCSPBLPAff.Characterization

namespace PCSPBLPAff.Characterization.O15aux

variable {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]

/-- coordinates of an LP point. -/
abbrev Coord (X : Instance τ ar) (A : Type) : Type :=
  (Fin X.n × A) ⊕ (Σ j : Fin X.m, (Fin (ar (X.sym j)) → A))

def coord (X : Instance τ ar) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) : Coord X A → ℚ
  | .inl ia => w ia.1 ia.2
  | .inr jy => p jy.1 jy.2

theorem coord_nonneg {X : Instance τ ar} {𝔸 : RelStruct τ ar A} {w p} (h : IsLPSol X 𝔸 w p)
    (c : Coord X A) : 0 ≤ coord X w p c := by
  rcases c with ⟨i, a⟩ | ⟨j, y⟩
  · exact h.1 i a
  · exact h.2.1 j y

theorem isLPSol_mid {X : Instance τ ar} {𝔸 : RelStruct τ ar A} {w p w' p'}
    (h : IsLPSol X 𝔸 w p) (h' : IsLPSol X 𝔸 w' p') :
    IsLPSol X 𝔸 (fun i a => (w i a + w' i a) / 2) (fun j y => (p j y + p' j y) / 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := h'
  refine ⟨fun i a => by have := h1 i a; have := h1' i a; positivity,
    fun j y => by have := h2 j y; have := h2' j y; positivity,
    fun j y hy => by simp [h3 j y hy, h3' j y hy], fun i => ?_, fun j => ?_, fun j k a => ?_⟩
  · rw [← Finset.sum_div, Finset.sum_add_distrib, h4, h4']; norm_num
  · rw [← Finset.sum_div, Finset.sum_add_distrib, h5, h5']; norm_num
  · rw [← Finset.sum_div, Finset.sum_add_distrib, h6, h6']

theorem coord_mid (X : Instance τ ar) (w p w' p') (c : Coord X A) :
    coord X (A := A) (fun i a => (w i a + w' i a) / 2) (fun j y => (p j y + p' j y) / 2) c =
      (coord X w p c + coord X w' p' c) / 2 := by
  rcases c with ⟨i, a⟩ | ⟨j, y⟩ <;> rfl

/-- A feasible LP has a solution of maximal support. -/
theorem exists_maxSupport {X : Instance τ ar} {𝔸 : RelStruct τ ar A} {w₀ p₀}
    (h₀ : IsLPSol X 𝔸 w₀ p₀) : ∃ w p, IsMaxSupportLPSol X 𝔸 w p := by
  classical
  have key : ∀ s : Finset (Coord X A), ∃ w p, IsLPSol X 𝔸 w p ∧ ∀ c ∈ s,
      (∃ w' p', IsLPSol X 𝔸 w' p' ∧ coord X w' p' c ≠ 0) → coord X w p c ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨w₀, p₀, h₀, by simp⟩
    | insert c s _ ih =>
      obtain ⟨w, p, hwp, hs⟩ := ih
      by_cases hc : ∃ w' p', IsLPSol X 𝔸 w' p' ∧ coord X w' p' c ≠ 0
      · obtain ⟨w', p', hwp', hc'⟩ := hc
        refine ⟨_, _, isLPSol_mid hwp hwp', fun d hd hex => ?_⟩
        rw [coord_mid]
        have a0 := coord_nonneg hwp d
        have b0 := coord_nonneg hwp' d
        rcases Finset.mem_insert.1 hd with rfl | hd
        · have : 0 < coord X w' p' d := lt_of_le_of_ne b0 (Ne.symm hc')
          positivity
        · have : 0 < coord X w p d := lt_of_le_of_ne a0 (Ne.symm (hs d hd hex))
          positivity
      · refine ⟨w, p, hwp, fun d hd hex => ?_⟩
        rcases Finset.mem_insert.1 hd with rfl | hd
        · exact absurd hex hc
        · exact hs d hd hex
  obtain ⟨w, p, hwp, hall⟩ := key Finset.univ
  refine ⟨w, p, hwp, fun w' p' h' => ⟨fun i a hne => ?_, fun j y hne => ?_⟩⟩
  · exact hall (.inl (i, a)) (Finset.mem_univ _) ⟨w', p', h', hne⟩
  · exact hall (.inr ⟨j, y⟩) (Finset.mem_univ _) ⟨w', p', h', hne⟩

/-- `Accepts ⇒ SatIn F`. -/
theorem sat_free_of_accepts {𝔸 : RelStruct τ ar A} {X : Instance τ ar} (h : Accepts 𝔸 X) :
    SatIn X (freeStruct 𝔸) := by
  obtain ⟨w, p, ⟨hlp, -⟩, r, q, ⟨hq0, hr1, hq1, hqm⟩, hrw, hqp⟩ := h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hlp
  refine ⟨fun i => ⟨(w i, r i), h1 i, h4 i, hr1 i, hrw i⟩, fun j => ?_⟩
  refine ⟨p j, q j, ⟨h2 j, h5 j, hq1 j, hqp j⟩, h3 j, fun k => ?_⟩
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · exact (h6 j k a).symm
  · exact (hqm j k a).symm

/-- `SatIn F ⇒ Accepts`. -/
theorem accepts_of_sat_free {𝔸 : RelStruct τ ar A} {X : Instance τ ar}
    (h : SatIn X (freeStruct 𝔸)) : Accepts 𝔸 X := by
  obtain ⟨σ, hσ⟩ := h
  choose p q hpq hvan hmarg using hσ
  have hlp : IsLPSol X 𝔸 (fun i a => (σ i).1.1 a) p := by
    refine ⟨fun i a => (σ i).2.1 a, fun j y => (hpq j).1 y, hvan, fun i => (σ i).2.2.1,
      fun j => (hpq j).2.1, fun j k a => ?_⟩
    exact (congrFun (congrArg Prod.fst (hmarg j k)) a).symm
  obtain ⟨w', p', hmax⟩ := exists_maxSupport hlp
  refine ⟨w', p', hmax, fun i a => (σ i).1.2 a, q, ⟨fun j y hy => (hpq j).2.2.2 y (hvan j y hy),
    fun i => (σ i).2.2.2.1, fun j => (hpq j).2.2.1, fun j k a => ?_⟩, fun i a h0 => ?_,
    fun j y h0 => ?_⟩
  · exact (congrFun (congrArg Prod.snd (hmarg j k)) a).symm
  · apply (σ i).2.2.2.2 a
    by_contra hne
    exact (hmax.2 _ _ hlp).1 i a hne h0
  · apply (hpq j).2.2.2 y
    by_contra hne
    exact (hmax.2 _ _ hlp).2 j y hne h0

theorem delta_obj {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι) :
    IsBLPAffObj (fun b => if b = a then (1 : ℚ) else 0) (fun b => if b = a then (1 : ℤ) else 0) := by
  refine ⟨fun b => ?_, by simp, by simp, fun b hb => ?_⟩
  · dsimp only; split_ifs <;> norm_num
  · dsimp only at hb ⊢; split_ifs at hb ⊢ <;> simp_all

/-- `SatIn 𝔸 ⇒ SatIn F` (dictator embedding `a ↦ (δ_a, δ_a)`). -/
theorem sat_free_of_sat {𝔸 : RelStruct τ ar A} {X : Instance τ ar} (h : SatIn X 𝔸) :
    SatIn X (freeStruct 𝔸) := by
  obtain ⟨σ, hσ⟩ := h
  let δ : A → FreeDom A := fun a =>
    ⟨(fun b => if b = a then 1 else 0, fun b => if b = a then 1 else 0), delta_obj a⟩
  refine ⟨fun i => δ (σ i), fun j => ?_⟩
  refine ⟨fun y => if y = σ ∘ X.scope j then 1 else 0, fun y => if y = σ ∘ X.scope j then 1 else 0,
    delta_obj _, fun y hy => if_neg (fun h : y = σ ∘ X.scope j => hy (h ▸ hσ j)), fun k => ?_⟩
  show (δ (σ (X.scope j k))).1 = _
  refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
  · show (if a = σ (X.scope j k) then (1 : ℚ) else 0) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a),
        (if y = σ ∘ X.scope j then (1 : ℚ) else 0)
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    rcases eq_or_ne a (σ (X.scope j k)) with h | h
    · simp [h]
    · simp [h, h.symm]
  · show (if a = σ (X.scope j k) then (1 : ℤ) else 0) =
      ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a),
        (if y = σ ∘ X.scope j then (1 : ℤ) else 0)
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    rcases eq_or_ne a (σ (X.scope j k)) with h | h
    · simp [h]
    · simp [h, h.symm]

end PCSPBLPAff.Characterization.O15aux

open PCSPBLPAff.Characterization.O15aux in
theorem PCSPBLPAff.Characterization.observation_15_main {τ : Type} {ar : τ → ℕ} {A B : Type}
    [Fintype A] [DecidableEq A] (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) :
    CorrectlySolves 𝔸 𝔹 ↔ ∀ X : Instance τ ar, SatIn X (freeStruct 𝔸) → SatIn X 𝔹 := by
  constructor
  · intro h X hX
    exact (h X).2 (accepts_of_sat_free hX)
  · intro h X
    exact ⟨fun hA => accepts_of_sat_free (sat_free_of_sat hA),
      fun hacc => h X (sat_free_of_accepts hacc)⟩

open PCSPBLPAff.Characterization in
/-- Observation 15, pp. 14–15. -/
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] (𝔸 : PCSPBLPAff.Symmetric.RelStruct τ ar A) (𝔹 : PCSPBLPAff.Symmetric.RelStruct τ ar B) (hT : PCSPBLPAff.Symmetric.IsPromiseTemplate 𝔸 𝔹) :
    PCSPBLPAff.Symmetric.CorrectlySolves 𝔸 𝔹 ↔ ∀ X : PCSPBLPAff.Symmetric.Instance τ ar, PCSPBLPAff.Symmetric.SatIn X (freeStruct 𝔸) → PCSPBLPAff.Symmetric.SatIn X 𝔹 :=
  PCSPBLPAff.Characterization.observation_15_main 𝔸 𝔹
