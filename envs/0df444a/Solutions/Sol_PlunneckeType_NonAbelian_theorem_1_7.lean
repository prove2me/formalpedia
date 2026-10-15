-- Prove2me | solution 1 for PlunneckeType.NonAbelian.theorem_1_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T04:18:52.120472+00:00
-- url     : https://prove2.me/submissions/728a69d9-7faf-4258-bc40-2e98a2683d37

import Mathlib

open scoped Pointwise
open Finset

set_option autoImplicit false

namespace P417

/-- KKT condition for the minimiser of a symmetric quadratic form on the standard simplex:
there is a probability vector `v` with `(M v)_b ≥ vᵀ M v` for every coordinate `b`. -/
theorem kkt_simplex {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (M : ι → ι → ℝ)
    (hM : ∀ i j, M i j = M j i) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
      ∀ b, (∑ i, ∑ j, v i * v j * M i j) ≤ ∑ j, v j * M b j := by
  set q : (ι → ℝ) → ℝ := fun v => ∑ i, ∑ j, v i * v j * M i j with hq
  have hne : (stdSimplex ℝ ι).Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨fun j => if j = i then 1 else 0, fun j => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp
  have hcont : Continuous q := by
    simp only [hq]; fun_prop
  obtain ⟨v, hv, hmin⟩ := (isCompact_stdSimplex ℝ ι).exists_isMinOn hne hcont.continuousOn
  refine ⟨v, hv.1, hv.2, fun b => ?_⟩
  by_contra hlt
  push_neg at hlt
  set m := ∑ j, v j * M b j with hm
  set s : ι → ℝ := fun j => if j = b then 1 else 0 with hs
  have hexp : ∀ ε : ℝ, q (fun j => (1 - ε) * v j + ε * s j) =
      (1 - ε) ^ 2 * q v + 2 * ε * (1 - ε) * m + ε ^ 2 * M b b := by
    intro ε
    have hrow : ∀ i, ∑ j, ((1 - ε) * v i + ε * s i) * ((1 - ε) * v j + ε * s j) * M i j
        = (1 - ε) ^ 2 * ∑ j, v i * v j * M i j + (1 - ε) * ε * (v i * M i b)
          + ε * (1 - ε) * (s i * ∑ j, v j * M i j) + ε ^ 2 * (s i * M i b) := by
      intro i
      have hsum : ∑ j, s j * M i j = M i b := by simp [hs]
      rw [← hsum]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have e1 : ∑ i, v i * M i b = m := by
      rw [hm]; exact Finset.sum_congr rfl (fun i _ => by rw [hM])
    have e2 : ∑ i, s i * ∑ j, v j * M i j = m := by
      simp [hs, hm]
    have e3 : ∑ i, s i * M i b = M b b := by simp [hs]
    simp only [hq]
    rw [Finset.sum_congr rfl (fun i _ => hrow i)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2, e3]
    ring
  have hmemw : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      (fun j => (1 - ε) * v j + ε * s j) ∈ stdSimplex ℝ ι := by
    intro ε h0 h1
    refine ⟨fun j => ?_, ?_⟩
    · have : 0 ≤ s j := by simp only [hs]; split_ifs <;> norm_num
      have := hv.1 j
      have : 0 ≤ 1 - ε := by linarith
      positivity
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hv.2, hs]
      simp
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      q v ≤ (1 - ε) ^ 2 * q v + 2 * ε * (1 - ε) * m + ε ^ 2 * M b b := by
    intro ε h0 h1
    rw [← hexp ε]
    exact (isMinOn_iff.mp hmin) _ (hmemw ε h0.le h1)
  set d := q v - m with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set C := q v - 2 * m + M b b with hC
  set ε := d / (|C| + d) with hε
  have hden : 0 < |C| + d := by positivity
  have hεpos : 0 < ε := div_pos hdpos hden
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_one hden]; linarith [abs_nonneg C]
  have hεd : ε * (|C| + d) = d := by rw [hε]; field_simp
  have h := key ε hεpos hε1
  have h2 : 0 ≤ ε * (-2 * d + ε * C) := by
    have : (1 - ε) ^ 2 * q v + 2 * ε * (1 - ε) * m + ε ^ 2 * M b b - q v
        = ε * (-2 * d + ε * C) := by rw [hd, hC]; ring
    linarith
  have h3 : 0 ≤ -2 * d + ε * C := by
    by_contra hneg; push_neg at hneg; nlinarith
  have h4 : ε * C ≤ ε * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hεpos.le
  have h5 : 2 * d ≤ ε * |C| := by linarith
  have h6 : 2 * d * (|C| + d) ≤ ε * |C| * (|C| + d) :=
    mul_le_mul_of_nonneg_right h5 hden.le
  have h7 : ε * |C| * (|C| + d) = d * |C| := by
    calc ε * |C| * (|C| + d) = (ε * (|C| + d)) * |C| := by ring
      _ = d * |C| := by rw [hεd]
  nlinarith [abs_nonneg C]

/-- Membership in a right translate. -/
theorem mem_mul_singleton_iff {G : Type*} [Group G] [DecidableEq G] (A : Finset G) (y c : G) :
    y ∈ A * {c} ↔ y * c⁻¹ ∈ A := by
  constructor
  · intro hy
    obtain ⟨a, ha, d, hd, rfl⟩ := Finset.mem_mul.1 hy
    rw [Finset.mem_singleton] at hd
    subst hd
    simpa using ha
  · intro hy
    exact Finset.mem_mul.2 ⟨y * c⁻¹, hy, c, Finset.mem_singleton_self c, by group⟩

/-- Main estimate (no minimality needed): `|ABB| |A|² ≤ |AB| |AA⁻¹| β |A|`. -/
theorem abb_bound {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (β : ℝ)
    (hB : B.Nonempty)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A) :
    (#(A * B * B) : ℝ) * (#A : ℝ) ^ 2 ≤ #(A * B) * (#(A * A⁻¹) * (β * #A)) := by
  classical
  haveI : Nonempty B := hB.to_subtype
  set f : B → G → ℝ := fun i y => if y ∈ A * {(i : G)} then 1 else 0 with hf
  set M : B → B → ℝ := fun i j => ∑ y ∈ A * B, f i y * f j y with hMdef
  have hMsym : ∀ i j, M i j = M j i := fun i j => by
    simp only [hMdef]; exact Finset.sum_congr rfl (fun y _ => mul_comm _ _)
  obtain ⟨v, hv0, hv1, hkkt⟩ := kkt_simplex M hMsym
  set q := ∑ i, ∑ j, v i * v j * M i j with hq
  -- Cauchy–Schwarz: |A|² ≤ |AB| q
  have hF : ∀ i : B, ∑ y ∈ A * B, f i y = #A := by
    intro i
    have hsub : A * {(i : G)} ⊆ A * B :=
      Finset.mul_subset_mul_left (Finset.singleton_subset_iff.2 i.2)
    simp only [hf]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub,
      Finset.card_mul_singleton]
  have hqy : q = ∑ y ∈ A * B, (∑ i, v i * f i y) ^ 2 := by
    calc q = ∑ i, ∑ j, ∑ y ∈ A * B, (v i * f i y) * (v j * f j y) := by
            simp only [hq, hMdef, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ i, ∑ y ∈ A * B, ∑ j, (v i * f i y) * (v j * f j y) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ y ∈ A * B, ∑ i, ∑ j, (v i * f i y) * (v j * f j y) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun y _ => by rw [sq, Finset.sum_mul_sum]
  have hsumF : ∑ y ∈ A * B, ∑ i, v i * f i y = #A := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hF, ← Finset.sum_mul, hv1, one_mul]
  have hCS : (#A : ℝ) ^ 2 ≤ #(A * B) * q := by
    rw [hqy, ← hsumF]
    exact sq_sum_le_card_mul_sum_sq
  -- representatives
  have hrep : ∀ x ∈ A * B * B, ∃ s ∈ A, ∃ b ∈ B, ∃ b' ∈ B, s * b * b' = x := by
    intro x hx
    obtain ⟨y, hy, b', hb', rfl⟩ := Finset.mem_mul.1 hx
    obtain ⟨s, hs, b, hb, rfl⟩ := Finset.mem_mul.1 hy
    exact ⟨s, hs, b, hb, b', hb', rfl⟩
  choose! sx hsx bx hbx bx' hbx' hx using hrep
  -- lower bound on the weighted counts
  have hMN : ∀ x (hxm : x ∈ A * B * B), ∀ t : B, M ⟨bx x, hbx x hxm⟩ t ≤
      (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ) := by
    intro x hxm t
    have hcnt : M ⟨bx x, hbx x hxm⟩ t =
        #((A * B).filter (fun y => y ∈ A * {bx x} ∧ y ∈ A * {(t : G)})) := by
      simp only [hMdef, hf, ite_zero_mul_ite_zero, mul_one]
      rw [Finset.sum_boole]
    rw [hcnt]
    exact_mod_cast Finset.card_le_card_of_injOn (fun y => y * (bx x)⁻¹)
      (by
        intro y hy
        rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
        refine ⟨(mem_mul_singleton_iff A y (bx x)).1 hy.2.1, ?_⟩
        simpa using hy.2.2)
      (by
        intro y _ y' _ hyy
        simpa using hyy)
  -- injection count for a fixed t
  have hinj : ∀ t : B, (∑ x ∈ A * B * B,
      (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ)) ≤
      #(A * A⁻¹) * #(A * {(t : G)} * B) := by
    intro t
    have hcard : ∑ x ∈ A * B * B, #(A.filter (fun u => u * bx x ∈ A * {(t : G)}))
        = #(((A * B * B) ×ˢ A).filter (fun p => p.2 * bx p.1 ∈ A * {(t : G)})) := by
      rw [Finset.card_filter, Finset.sum_product]
      simp only [Finset.card_filter]
    have hle : #(((A * B * B) ×ˢ A).filter (fun p => p.2 * bx p.1 ∈ A * {(t : G)})) ≤
        #((A * A⁻¹) ×ˢ (A * {(t : G)} * B)) := by
      apply Finset.card_le_card_of_injOn (fun p => (sx p.1 * p.2⁻¹, p.2 * bx p.1 * bx' p.1))
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
        rw [Finset.mem_coe, Finset.mem_product]
        exact ⟨Finset.mul_mem_mul (hsx _ hp1) (Finset.inv_mem_inv hp2),
          Finset.mul_mem_mul hp3 (hbx' _ hp1)⟩
      · intro p hp p' hp' heq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp hp'
        have hp1 := hp.1.1
        have hp1' := hp'.1.1
        simp only [Prod.mk.injEq] at heq
        obtain ⟨e1, e2⟩ := heq
        have hxx : p.1 = p'.1 := by
          have h12 := congrArg₂ (· * ·) e1 e2
          rw [← hx _ hp1, ← hx _ hp1']
          simpa [mul_assoc] using h12
        have huu : p.2 = p'.2 := by
          rw [hxx] at e1
          exact inv_injective (mul_left_cancel e1)
        exact Prod.ext hxx huu
    rw [← Nat.cast_mul, ← Finset.card_product]
    exact_mod_cast (hcard ▸ hle)
  -- assemble
  set P := (#(A * A⁻¹) : ℝ) with hP
  have hlow : (#(A * B * B) : ℝ) * q ≤
      ∑ x ∈ A * B * B, ∑ t : B, v t * (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ) := by
    have hconst : (#(A * B * B) : ℝ) * q = ∑ x ∈ A * B * B, q := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    refine Finset.sum_le_sum fun x hxm => ?_
    calc q ≤ ∑ t : B, v t * M ⟨bx x, hbx x hxm⟩ t := hkkt _
      _ ≤ _ := Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (hMN x hxm t) (hv0 t)
  have hup : ∑ x ∈ A * B * B, ∑ t : B, v t * (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ)
      ≤ P * (β * #A) := by
    rw [Finset.sum_comm]
    calc ∑ t : B, ∑ x ∈ A * B * B, v t * (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ)
        = ∑ t : B, v t * ∑ x ∈ A * B * B,
            (#(A.filter (fun u => u * bx x ∈ A * {(t : G)})) : ℝ) := by
          exact Finset.sum_congr rfl fun t _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ t : B, v t * (P * (β * #A)) := by
          refine Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (hv0 t)
          calc _ ≤ P * #(A * {(t : G)} * B) := hinj t
            _ ≤ P * (β * #A) := mul_le_mul_of_nonneg_left (h2 _ t.2) (by positivity)
      _ = P * (β * #A) := by rw [← Finset.sum_mul, hv1, one_mul]
  have hq0 : 0 ≤ (#(A * B * B) : ℝ) := by positivity
  calc (#(A * B * B) : ℝ) * (#A : ℝ) ^ 2 ≤ #(A * B * B) * (#(A * B) * q) :=
        mul_le_mul_of_nonneg_left hCS hq0
    _ = #(A * B) * (#(A * B * B) * q) := by ring
    _ ≤ #(A * B) * (P * (β * #A)) :=
        mul_le_mul_of_nonneg_left (hlow.trans hup) (Nat.cast_nonneg _)

end P417

open Finset Pointwise in
theorem solution {G : Type*} [Group G] [DecidableEq G] (A B : Finset G) (α β γ : ℝ)
    (hA : A.Nonempty)
    (h1 : (#(A * B) : ℝ) ≤ α * #A)
    (h2 : ∀ b ∈ B, (#(A * {b} * B) : ℝ) ≤ β * #A)
    (h3 : (#A : ℝ) ≤ γ * #B) :
    ∃ S ⊆ A, S.Nonempty ∧ ∀ h : ℕ, 1 < h →
      (#(S * B ^ h) : ℝ) ≤ α ^ (8 * h - 9) * β ^ (h - 1) * γ ^ (4 * h - 5) * #S := by
  classical
  have hApos : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hBne : B.Nonempty := by
    rcases B.eq_empty_or_nonempty with hB | hB
    · exfalso; rw [hB, Finset.card_empty, Nat.cast_zero, mul_zero] at h3; linarith
    · exact hB
  have hBpos : (0 : ℝ) < #B := by exact_mod_cast hBne.card_pos
  have hAB_ge : (#A : ℝ) ≤ #(A * B) := by exact_mod_cast Finset.card_le_card_mul_right hBne
  have hB_le : (#B : ℝ) ≤ #(A * B) := by exact_mod_cast Finset.card_le_card_mul_left hA
  have hα1 : 1 ≤ α := by
    have : (#A : ℝ) ≤ α * #A := hAB_ge.trans h1
    by_contra hc; push_neg at hc; nlinarith
  have hα0 : 0 ≤ α := by linarith
  have hγpos : 0 < γ := by
    by_contra hc; push_neg at hc; nlinarith
  have hγ0 : 0 ≤ γ := hγpos.le
  have hαγ : 1 ≤ α * γ := by
    have : (#A : ℝ) ≤ γ * (α * #A) :=
      h3.trans (mul_le_mul_of_nonneg_left (hB_le.trans h1) hγ0)
    nlinarith
  have hβ0 : 0 ≤ β := by
    obtain ⟨b, hb⟩ := hBne
    have hb2 := h2 b hb
    have : (0 : ℝ) ≤ β * #A := le_trans (by positivity) hb2
    by_contra hc; push_neg at hc; nlinarith
  have hR1 : (#(A * A⁻¹) : ℝ) * #B ≤ #(A * B) * #(A * B) := by
    exact_mod_cast ruzsa_triangle_inequality_mulInv_mul_mul A B A
  have hmain := P417.abb_bound A B β hBne h2
  set a := (#A : ℝ) with ha
  set n := (#B : ℝ) with hn
  set p := (#(A * B) : ℝ) with hp
  set P := (#(A * A⁻¹) : ℝ) with hP
  set X := (#(A * B * B) : ℝ) with hX
  have hp0 : 0 ≤ p := by positivity
  have hABB : X ≤ α ^ 3 * β * γ * a := by
    have e2 : p ^ 3 ≤ (α * a) ^ 3 := pow_le_pow_left₀ hp0 h1 3
    have hmul : X * (a ^ 2 * n) ≤ (α ^ 3 * β * γ * a) * (a ^ 2 * n) := by
      calc X * (a ^ 2 * n) = X * a ^ 2 * n := by ring
        _ ≤ p * (P * (β * a)) * n := mul_le_mul_of_nonneg_right hmain hBpos.le
        _ = p * β * a * (P * n) := by ring
        _ ≤ p * β * a * (p * p) := mul_le_mul_of_nonneg_left hR1 (by positivity)
        _ = β * a * p ^ 3 := by ring
        _ ≤ β * a * (α * a) ^ 3 := mul_le_mul_of_nonneg_left e2 (by positivity)
        _ = (α ^ 3 * β * a ^ 3) * a := by ring
        _ ≤ (α ^ 3 * β * a ^ 3) * (γ * n) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (α ^ 3 * β * γ * a) * (a ^ 2 * n) := by ring
    exact le_of_mul_le_mul_right hmul (by positivity)
  set c := α ^ 4 * β * γ ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set D := (#(A * B * A⁻¹) : ℝ) with hD
  have hR2 : D * n ≤ X * p := by
    rw [hD, hn, hX, hp]
    exact_mod_cast ruzsa_triangle_inequality_mulInv_mul_mul (A * B) B A
  have hDle : D ≤ c * a := by
    have hmul : D * n ≤ (c * a) * n := by
      calc D * n ≤ X * p := hR2
        _ ≤ (α ^ 3 * β * γ * a) * (α * a) :=
            mul_le_mul hABB h1 hp0 (by positivity)
        _ = (α ^ 4 * β * γ * a) * a := by ring
        _ ≤ (α ^ 4 * β * γ * a) * (γ * n) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = (c * a) * n := by rw [hc]; ring
    exact le_of_mul_le_mul_right hmul hBpos
  have hstep : ∀ j : ℕ, (#(A * B ^ (j + 1)) : ℝ) ≤ c * #(A * B ^ j) := by
    intro j
    have hr : #(A * B * B ^ j) * #A ≤ #(A * B * A⁻¹) * #(A * B ^ j) := by
      have h0 := ruzsa_triangle_inequality_mul_mul_invMul (A * B) A⁻¹ (B ^ j)
      rw [Finset.card_inv] at h0
      have e2 : (B ^ j)⁻¹ * A⁻¹ = (A * B ^ j)⁻¹ := (mul_inv_rev _ _).symm
      rw [e2, Finset.card_inv] at h0
      exact h0
    rw [pow_succ', ← mul_assoc]
    have hr' : (#(A * B * B ^ j) : ℝ) * a ≤ D * #(A * B ^ j) := by
      rw [ha, hD]; exact_mod_cast hr
    have hmul : (#(A * B * B ^ j) : ℝ) * a ≤ (c * #(A * B ^ j)) * a := by
      calc (#(A * B * B ^ j) : ℝ) * a ≤ D * #(A * B ^ j) := hr'
        _ ≤ (c * a) * #(A * B ^ j) := mul_le_mul_of_nonneg_right hDle (by positivity)
        _ = (c * #(A * B ^ j)) * a := by ring
    exact le_of_mul_le_mul_right hmul hApos
  have hind : ∀ k : ℕ, (#(A * B ^ (k + 2)) : ℝ) ≤ α ^ 3 * β * γ * c ^ k * a := by
    intro k
    induction k with
    | zero =>
      have e : A * B ^ (0 + 2) = A * B * B := by rw [zero_add, sq, ← mul_assoc]
      rw [e, pow_zero, mul_one]
      exact hABB
    | succ k ih =>
      calc (#(A * B ^ (k + 1 + 2)) : ℝ) = #(A * B ^ ((k + 2) + 1)) := by
            rw [show k + 1 + 2 = (k + 2) + 1 by omega]
        _ ≤ c * #(A * B ^ (k + 2)) := hstep (k + 2)
        _ ≤ c * (α ^ 3 * β * γ * c ^ k * a) := mul_le_mul_of_nonneg_left ih hc0
        _ = α ^ 3 * β * γ * c ^ (k + 1) * a := by ring
  refine ⟨A, Finset.Subset.refl _, hA, ?_⟩
  intro h hh
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
  have e1 : 8 * (k + 2) - 9 = 8 * k + 7 := by omega
  have e2 : k + 2 - 1 = k + 1 := by omega
  have e3 : 4 * (k + 2) - 5 = 4 * k + 3 := by omega
  rw [e1, e2, e3]
  have hid : α ^ (8 * k + 7) * β ^ (k + 1) * γ ^ (4 * k + 3) * a
      = (α ^ 3 * β * γ * c ^ k * a) * (α ^ 2 * γ) ^ (2 * k + 2) := by
    rw [hc]; ring
  have hge : 1 ≤ (α ^ 2 * γ) ^ (2 * k + 2) := by
    apply one_le_pow₀
    nlinarith
  rw [hid]
  calc (#(A * B ^ (k + 2)) : ℝ) ≤ α ^ 3 * β * γ * c ^ k * a := hind k
    _ = (α ^ 3 * β * γ * c ^ k * a) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
