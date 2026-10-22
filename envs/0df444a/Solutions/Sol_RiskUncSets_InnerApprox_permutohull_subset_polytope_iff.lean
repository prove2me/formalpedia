-- Prove2me | solution 1 for RiskUncSets.InnerApprox.permutohull_subset_polytope_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:59:18.383861+00:00
-- url     : https://prove2.me/submissions/134f4ea0-a97e-476a-9bae-c2bc870fb332

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section


namespace RiskUncSets.InnerApprox

variable {α : Type*} [Fintype α] [DecidableEq α] (b : α → α → ℝ)

/-- reversed path weight: list x :: y :: l has edge y → x. -/
def hwcPW : List α → ℝ
  | x :: y :: l => b y x + hwcPW (y :: l)
  | _ => 0

lemma hwcPW_append (A B : List α) (s : α) :
    hwcPW b (A ++ s :: B) = hwcPW b (A ++ [s]) + hwcPW b (s :: B) := by
  induction A with
  | nil => simp [hwcPW]
  | cons x A ih =>
    cases A with
    | nil =>
      cases B <;> simp [hwcPW]
    | cons y A =>
      simp only [List.cons_append, hwcPW] at ih ⊢
      rw [ih]; ring

lemma hwc_swap_sum (ρ : Equiv.Perm α) (x y : α) (hxy : x ≠ y) (hx : ρ x = x) :
    ∑ t, b ((Equiv.swap x y * ρ) t) t
      = ∑ t, b (ρ t) t + b y x + b x (ρ.symm y) - b x x - b y (ρ.symm y) := by
  have e1 : ∀ g : α → α → ℝ, ∑ t, g (ρ t) t = ∑ u, g u (ρ.symm u) := by
    intro g
    rw [← Equiv.sum_comp ρ (fun u => g u (ρ.symm u))]
    simp
  have hxs : ρ.symm x = x := by rw [Equiv.symm_apply_eq]; exact hx.symm
  simp only [Equiv.Perm.coe_mul, Function.comp]
  rw [e1 (fun u t => b (Equiv.swap x y u) t), e1 (fun u t => b u t)]
  have : ∑ u, b (Equiv.swap x y u) (ρ.symm u) - ∑ u, b u (ρ.symm u)
      = (b (Equiv.swap x y x) (ρ.symm x) - b x (ρ.symm x))
        + (b (Equiv.swap x y y) (ρ.symm y) - b y (ρ.symm y)) := by
    rw [← Finset.sum_sub_distrib]
    apply Fintype.sum_eq_add x y hxy
    intro u hu
    rw [Equiv.swap_apply_of_ne_of_ne hu.1 hu.2]; ring
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, hxs] at this
  linarith

lemma hwc_cycle (hb0 : ∀ t, b t t = 0) :
    ∀ (l : List α) (y : α), (y :: l).Nodup →
      ∑ t, b ((y :: l).formPerm t) t = hwcPW b (y :: l) + b y ((y :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil =>
    intro y _
    simp [hwcPW, hb0]
  | cons z l ih =>
    intro y hnd
    have hy : y ∉ z :: l := (List.nodup_cons.mp hnd).1
    have hnd' : (z :: l).Nodup := (List.nodup_cons.mp hnd).2
    have hyz : y ≠ z := fun h => hy (h ▸ List.mem_cons_self)
    rw [List.formPerm_cons_cons, hwc_swap_sum b _ y z hyz (List.formPerm_apply_of_notMem hy), ih z hnd']
    have hl : (z :: l).formPerm.symm z = (z :: l).getLast (List.cons_ne_nil _ _) := by
      rw [Equiv.symm_apply_eq]; simp
    rw [hl]
    have : (y :: z :: l).getLast (List.cons_ne_nil _ _) = (z :: l).getLast (List.cons_ne_nil _ _) :=
      List.getLast_cons _
    rw [this, hb0]
    simp only [hwcPW]; ring

theorem hwc_potential (hb0 : ∀ t, b t t = 0) (hperm : ∀ ρ : Equiv.Perm α, 0 ≤ ∑ t, b (ρ t) t) :
    ∃ π : α → ℝ, ∀ t s, π s ≤ π t + b t s := by
  classical
  set M : ℝ := ∑ u, ∑ v, |b u v| with hM
  have hM0 : ∀ u v, -M ≤ b u v := by
    intro u v
    have h1 : |b u v| ≤ ∑ v, |b u v| :=
      Finset.single_le_sum (f := fun v => |b u v|) (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    have h2 : ∑ v, |b u v| ≤ M :=
      Finset.single_le_sum (f := fun u => ∑ v, |b u v|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)
    linarith [neg_abs_le (b u v)]
  have hMnn : 0 ≤ M := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlow : ∀ l : List α, -(l.length : ℝ) * M ≤ hwcPW b l := by
    intro l
    induction l with
    | nil => simp [hwcPW]
    | cons x l ih =>
      cases l with
      | nil => simp [hwcPW]; exact hMnn
      | cons y l =>
        simp only [hwcPW, List.length_cons] at ih ⊢
        push_cast at ih ⊢
        linarith [hM0 y x]
  let S : α → Set ℝ := fun s => {r | ∃ l : List α, (s :: l).Nodup ∧ r = hwcPW b (s :: l)}
  have hbdd : ∀ s, BddBelow (S s) := by
    intro s
    refine ⟨-(Fintype.card α : ℝ) * M, ?_⟩
    rintro r ⟨l, hl, rfl⟩
    have := hlow (s :: l)
    have hlen : ((s :: l).length : ℝ) ≤ Fintype.card α := by exact_mod_cast hl.length_le_card
    nlinarith
  have hne : ∀ s, (S s).Nonempty := fun s => ⟨_, [], by simp, rfl⟩
  refine ⟨fun s => sInf (S s), ?_⟩
  intro t s
  show sInf (S s) ≤ sInf (S t) + b t s
  rw [← sub_le_iff_le_add]
  apply le_csInf (hne t)
  rintro r ⟨l, hl, rfl⟩
  rw [sub_le_iff_le_add]
  by_cases hs : s ∈ t :: l
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hs
    have hndB : (s :: B).Nodup := by
      rw [hAB] at hl; exact (List.nodup_append.mp hl).2.1
    have h1 : sInf (S s) ≤ hwcPW b (s :: B) := csInf_le (hbdd s) ⟨B, hndB, rfl⟩
    have h2 : 0 ≤ hwcPW b (A ++ [s]) + b t s := by
      cases A with
      | nil =>
        simp at hAB
        rw [hAB.1]; simp [hwcPW, hb0]
      | cons x A =>
        simp only [List.cons_append, List.cons.injEq] at hAB
        obtain ⟨rfl, hAB2⟩ := hAB
        have hndc : (t :: (A ++ [s])).Nodup := by
          have : (t :: l).Nodup := hl
          rw [hAB2] at this
          have h3 : (t :: A ++ s :: B).Nodup := this
          have h4 : ((t :: A ++ [s]) ++ B).Nodup := by simpa using h3
          exact (List.nodup_append.mp h4).1
        have := hwc_cycle b hb0 (A ++ [s]) t hndc
        have hlast : (t :: (A ++ [s])).getLast (List.cons_ne_nil _ _) = s := by
          simp
        rw [hlast] at this
        have := hperm (t :: (A ++ [s])).formPerm
        simp only [List.cons_append]
        linarith
    rw [hAB, hwcPW_append]
    linarith
  · have hnd : (s :: t :: l).Nodup := List.nodup_cons.mpr ⟨hs, hl⟩
    have := csInf_le (hbdd s) ⟨t :: l, hnd, rfl⟩
    simp only [hwcPW] at this
    linarith


lemma hwc_cost_comp' {n : ℕ} (c : Fin n → Fin n → ℝ) (σ ρ : Equiv.Perm (Fin n)) :
    ∑ t, (c t (σ.symm (ρ t)) - c (ρ t) (σ.symm (ρ t))) =
      ∑ r, c ((σ.trans ρ.symm) r) r - ∑ r, c (σ r) r := by
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [← Equiv.sum_comp (σ.trans ρ.symm) (fun t => c t (σ.symm (ρ t)))]
    simp
  · rw [Equiv.sum_comp ρ (fun u => c u (σ.symm u)), ← Equiv.sum_comp σ (fun u => c u (σ.symm u))]
    simp

lemma assign_dual {n : ℕ} (c : Fin n → Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hσ : ∀ τ : Equiv.Perm (Fin n), ∑ r, c (σ r) r ≤ ∑ r, c (τ r) r) :
    ∃ s t : Fin n → ℝ, ∑ i, (s i + t i) = ∑ r, c (σ r) r ∧ ∀ i j, s i + t j ≤ c i j := by
  obtain ⟨π, hπ⟩ := hwc_potential (fun t s => c s (σ.symm t) - c t (σ.symm t)) (by simp)
    (fun ρ => by rw [hwc_cost_comp']; linarith [hσ (σ.trans ρ.symm)])
  have key : ∀ r s, c (σ r) r - π (σ r) ≤ c s r - π s := by
    intro r s
    have := hπ (σ r) s
    simp at this
    linarith
  refine ⟨π, fun r => c (σ r) r - π (σ r), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp σ π]; ring
  · intro i j
    have := key j i
    linarith

lemma assign_dual_iff {n : ℕ} (c : Fin n → Fin n → ℝ) (V : ℝ) :
    (∀ τ : Equiv.Perm (Fin n), V ≤ ∑ r, c (τ r) r) ↔
      ∃ s t : Fin n → ℝ, V ≤ ∑ i, (s i + t i) ∧ ∀ i j, s i + t j ≤ c i j := by
  constructor
  · intro h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (fun τ => ∑ r, c (τ r) r) ⟨1, Finset.mem_univ _⟩
    obtain ⟨s, t, h1, h2⟩ := assign_dual c σ (fun τ => hσ τ (Finset.mem_univ _))
    exact ⟨s, t, by rw [h1]; exact h σ, h2⟩
  · rintro ⟨s, t, h1, h2⟩ τ
    refine h1.trans ?_
    rw [Finset.sum_add_distrib]
    calc ∑ i, s i + ∑ i, t i = ∑ r, s (τ r) + ∑ r, t r := by rw [Equiv.sum_comp τ s]
      _ = ∑ r, (s (τ r) + t r) := by rw [Finset.sum_add_distrib]
      _ ≤ _ := Finset.sum_le_sum fun r _ => h2 _ _

theorem permutohull_core {N n m : ℕ} (q : Fin N → ℝ)
    (a : Fin N → Fin n → ℝ) (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) :
    permutohull q a ⊆ polytope u v ↔
      ∃ s t : Fin m → Fin N → ℝ, (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
        ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i := by
  have step : ∀ k, (permutohull q a ⊆ {w | v k ≤ u k ⬝ᵥ w}) ↔
      ∃ s t : Fin N → ℝ, v k ≤ ∑ i, (s i + t i) ∧ ∀ i j, s i + t j ≤ (u k ⬝ᵥ a j) * q i := by
    intro k
    rw [← assign_dual_iff (fun i j => (u k ⬝ᵥ a j) * q i) (v k)]
    have hval : ∀ τ : Equiv.Perm (Fin N), u k ⬝ᵥ (∑ i, q (τ i) • a i) =
        ∑ r, (u k ⬝ᵥ a r) * q (τ r) := by
      intro τ
      simp [dotProduct_sum, dotProduct_smul, mul_comm]
    constructor
    · intro h τ
      have : (∑ i, q (τ i) • a i) ∈ permutohull q a := subset_convexHull ℝ _ ⟨τ, rfl⟩
      have := h this
      simp only [Set.mem_setOf_eq, hval] at this
      exact this
    · intro h
      unfold permutohull
      apply convexHull_min
      · rintro _ ⟨τ, rfl⟩
        simp only [Set.mem_setOf_eq, hval]
        exact h τ
      · -- halfspace is convex
        exact convex_halfSpace_ge (f := fun w => u k ⬝ᵥ w)
          ⟨fun x y => by simp [dotProduct_add], fun c x => by simp [dotProduct_smul]⟩ _
  have hsub : permutohull q a ⊆ polytope u v ↔ ∀ k, permutohull q a ⊆ {w | v k ≤ u k ⬝ᵥ w} := by
    constructor
    · intro h k w hw; exact h hw k
    · intro h w hw k; exact h k hw
  rw [hsub]
  simp only [step]
  constructor
  · intro h
    choose s t hs ht using h
    exact ⟨s, t, hs, ht⟩
  · rintro ⟨s, t, hs, ht⟩ k
    exact ⟨s k, t k, hs k, ht k⟩

end RiskUncSets.InnerApprox

open RiskUncSets.InnerApprox


theorem solution {N n m : ℕ} (q : Fin N → ℝ)
    (a : Fin N → Fin n → ℝ) (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) :
    permutohull q a ⊆ polytope u v ↔
      ∃ s t : Fin m → Fin N → ℝ, (∀ k, v k ≤ ∑ i, (s k i + t k i)) ∧
        ∀ k i j, s k i + t k j ≤ (u k ⬝ᵥ a j) * q i := by
  exact permutohull_core q a u v
