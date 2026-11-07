-- Prove2me | solution 1 for SendSplit.Existence.hirsch_hoffman_extension
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:35:15.398687+00:00
-- url     : https://prove2.me/submissions/26f43fae-4635-4183-9231-3323dbe6946e

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Theorems.Thm_SendSplit_Existence_concave_sandwich

open SendSplit.Existence
open Fin.NatCast


namespace SSHHAux

variable {n : ℕ}

lemma three_point (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (x0 x1 x2 : Fin n → Fin n → ℝ) (h1 : ∀ i j, 0 ≤ x1 i j) (h2 : ∀ i j, 0 ≤ x2 i j)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (h : ∀ i j, x0 i j = l * x1 i j + (1 - l) * x2 i j) :
    l * flowCost G c x1 + (1 - l) * flowCost G c x2 ≤ flowCost G c x0 := by
  unfold flowCost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have := (hc p hp).1.2 (Set.mem_Ici.2 (h1 p.1 p.2)) (Set.mem_Ici.2 (h2 p.1 p.2)) hl0
    (by linarith : (0:ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul] at this
  rw [h]; exact this

lemma flow_add_dir (G : ArcGraph n) (r : Fin n → ℝ) (x d : Fin n → Fin n → ℝ)
    (hx : IsFlow G r x) (hdoff : ∀ i j, (i, j) ∉ G.A → d i j = 0)
    (hdbal : ∀ i, (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), d j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), d i k) = 0)
    (t : ℝ) (hnn : ∀ i j, 0 ≤ x i j + t * d i j) :
    IsFlow G r (fun i j => x i j + t * d i j) := by
  obtain ⟨⟨_, hxo⟩, hxb⟩ := hx
  refine ⟨⟨hnn, fun i j h => by simp [hxo i j h, hdoff i j h]⟩, ?_⟩
  intro i
  have h1 := hxb i
  have h2 := hdbal i
  simp only
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have : t * (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), d j i)
      - t * (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), d i k) = 0 := by
    rw [← mul_sub, h2, mul_zero]
  linarith

lemma support_sub (G : ArcGraph n) (x d : Fin n → Fin n → ℝ)
    (hd : ∀ i j, x i j = 0 → d i j = 0) (t : ℝ) :
    support G (fun i j => x i j + t * d i j) ⊆ support G x := by
  intro p
  simp only [support, Finset.mem_filter, ne_eq]
  rintro ⟨hpA, hne⟩
  refine ⟨hpA, fun h0 => hne ?_⟩
  rw [h0, hd _ _ h0]; ring

lemma card_support_lt (G : ArcGraph n) (x d : Fin n → Fin n → ℝ)
    (hd : ∀ i j, x i j = 0 → d i j = 0) (t : ℝ) (p : Fin n × Fin n) (hp : p ∈ support G x)
    (h0 : x p.1 p.2 + t * d p.1 p.2 = 0) :
    (support G (fun i j => x i j + t * d i j)).card < (support G x).card := by
  apply Finset.card_lt_card
  refine (Finset.ssubset_iff_of_subset (support_sub G x d hd t)).2 ⟨p, hp, ?_⟩
  simp only [support, Finset.mem_filter, ne_eq, not_and, not_not]
  intro _; exact h0

/-- The indicator of a simple circuit is a simple circulation with that support. -/
lemma circuit_indicator (G : ArcGraph n) (C : Finset (Fin n × Fin n)) (hC : IsSimpleCircuit G C) :
    IsSimpleCirculation G (fun i j => if (i, j) ∈ C then 1 else 0) ∧
      support G (fun i j => if (i, j) ∈ C then 1 else 0) = C := by
  obtain ⟨m, v, hv, hA, rfl⟩ := hC
  set C := Finset.univ.image (fun k => (v k, v (k + 1))) with hCdef
  have hCA : ∀ p ∈ C, p ∈ G.A := by
    intro p hp
    rw [hCdef, Finset.mem_image] at hp
    obtain ⟨k, _, rfl⟩ := hp
    exact hA k
  have hsupp : support G (fun i j => if (i, j) ∈ C then 1 else 0) = C := by
    unfold support
    ext p
    simp only [Finset.mem_filter, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    exact ⟨fun h => h.2, fun h => ⟨hCA p h, h⟩⟩
  refine ⟨⟨⟨⟨fun i j => by dsimp only; split_ifs <;> norm_num, fun i j h => ?_⟩, ?_⟩, ?_⟩, hsupp⟩
  · dsimp only; rw [if_neg]; exact fun h' => h (hCA _ h')
  · intro i
    simp only
    rw [Finset.sum_boole, Finset.sum_boole, Finset.filter_filter, Finset.filter_filter]
    have hin : (Finset.univ.filter (fun j => (j, i) ∈ G.A ∧ (j, i) ∈ C)) =
        (Finset.univ.filter (fun k => v (k + 1) = i)).image v := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hCdef,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, k, h1, h2⟩
        exact ⟨k, h2, h1⟩
      · rintro ⟨k, h2, h1⟩
        refine ⟨?_, k, h1, h2⟩
        rw [← h1, ← h2]; exact hA k
    have hout : (Finset.univ.filter (fun j => (i, j) ∈ G.A ∧ (i, j) ∈ C)) =
        (Finset.univ.filter (fun k => v k = i)).image (fun k => v (k + 1)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hCdef,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, k, h1, h2⟩
        exact ⟨k, h1, h2⟩
      · rintro ⟨k, h1, h2⟩
        refine ⟨?_, k, h1, h2⟩
        rw [← h1, ← h2]; exact hA k
    have hshift : (Finset.univ.filter (fun k => v k = i)) =
        (Finset.univ.filter (fun k => v (k + 1) = i)).map
          (Equiv.addRight (1 : Fin (m + 2))).toEmbedding := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv]
      simp
    rw [hin, hout, Finset.card_image_of_injective _ hv,
      Finset.card_image_of_injective _
        (show Function.Injective (fun k : Fin (m + 2) => v (k + 1)) from
          hv.comp (add_left_injective 1)), hshift, Finset.card_map]
    simp
  · rw [hsupp]; exact ⟨m, v, hv, hA, rfl⟩

lemma rev_circuit (G : ArcGraph n) {m : ℕ} (v : Fin (m + 2) → Fin n) (hv : Function.Injective v)
    (hA : ∀ k, (v (k + 1), v k) ∈ G.A) :
    IsSimpleCircuit G (Finset.univ.image (fun k => (v (k + 1), v k))) := by
  refine ⟨m, fun k => v (-k), hv.comp neg_injective, fun k => ?_, ?_⟩
  · have := hA (-(k + 1))
    simp only at this ⊢
    rwa [show -(k + 1) + 1 = -k by abel] at this
  · ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨-(j + 1), ?_⟩
      rw [show -(-(j + 1)) = j + 1 by abel, show -(-(j + 1) + 1) = j by abel]
    · rintro ⟨k, rfl⟩
      refine ⟨-(k + 1), ?_⟩
      rw [show -(k + 1) + 1 = -k by abel]

end SSHHAux



namespace SSHHAux

variable {n : ℕ}

/-- The property that every simple circulation has nonnegative cost along its ray. -/
def RayNonneg (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) : Prop :=
  ∀ y, IsSimpleCirculation G y → ∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j)

lemma ray (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (P : RayNonneg G c) (x y : Fin n → Fin n → ℝ) (hx : IsPreflow G x)
    (hy : IsSimpleCirculation G y) (α : ℝ) (hα : 0 ≤ α)
    (hnn : ∀ i j, 0 ≤ x i j + (-α) * y i j) :
    flowCost G c (fun i j => x i j + (-α) * y i j) ≤ flowCost G c x := by
  by_contra hlt
  push Not at hlt
  rcases hα.eq_or_lt with h0 | hpos
  · subst h0
    have : (fun i j => x i j + (-0) * y i j) = x := by funext i j; ring
    rw [this] at hlt; exact lt_irrefl _ hlt
  set c0 := flowCost G c x
  set c1 := flowCost G c (fun i j => x i j + (-α) * y i j)
  set B := (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j)
  set D := c1 - c0 with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  set K := c0 - B
  set T := (α * |K| + 1) / D with hT
  have hTpos : 0 < T := by rw [hT]; positivity
  have hyn : ∀ i j, 0 ≤ y i j := hy.1.1.1
  have hx2 : ∀ i j, 0 ≤ x i j + T * y i j := fun i j =>
    add_nonneg (hx.1 i j) (mul_nonneg hTpos.le (hyn i j))
  have hTa : 0 < T + α := by linarith
  have h3 := three_point G c hc x (fun i j => x i j + (-α) * y i j)
    (fun i j => x i j + T * y i j) hnn hx2 (T / (T + α)) (by positivity)
    (by rw [div_le_one hTa]; linarith) (by intro i j; field_simp; ring)
  set c2 := flowCost G c (fun i j => x i j + T * y i j)
  have hsand := (concave_sandwich G c hc x y hx hy.1.1 T hTpos.le).1
  have hP := P y hy (2 * T) (by positivity)
  have e2 : (fun i j => 2 * (T * y i j)) = (fun i j => 2 * T * y i j) := by funext i j; ring
  rw [← e2] at hP
  have hc2 : B ≤ c2 := by
    have hB : B = (1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j) := rfl
    rw [hB]
    linarith [mul_le_mul_of_nonneg_left hP (by norm_num : (0:ℝ) ≤ 1 / 2)]
  have hmul := mul_le_mul_of_nonneg_right h3 hTa.le
  have e : (T / (T + α) * c1 + (1 - T / (T + α)) * c2) * (T + α) = T * c1 + α * c2 := by
    field_simp; ring
  rw [e] at hmul
  have hTD : T * D = α * |K| + 1 := by rw [hT]; field_simp
  have hK : α * K ≤ α * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hα
  have hc2' : α * B ≤ α * c2 := mul_le_mul_of_nonneg_left hc2 hα
  have : T * D = T * c1 - T * c0 := by rw [hD]; ring
  have hKdef : α * K = α * c0 - α * B := by ring
  nlinarith

lemma directed_case (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x)
    (C : Finset (Fin n × Fin n)) (hC : IsSimpleCircuit G C) (hCs : C ⊆ support G x) :
    ∃ x1, IsFlow G r x1 ∧ (support G x1).card < (support G x).card ∧
      (RayNonneg G c → flowCost G c x1 ≤ flowCost G c x) := by
  obtain ⟨hy, hysupp⟩ := circuit_indicator G C hC
  set y : Fin n → Fin n → ℝ := fun i j => if (i, j) ∈ C then 1 else 0 with hydef
  have hne : C.Nonempty := by
    obtain ⟨m, v, -, -, rfl⟩ := hC
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
  obtain ⟨p1, hp1, hmin⟩ := C.exists_min_image (fun p => x p.1 p.2) hne
  set α := x p1.1 p1.2
  have hα : 0 ≤ α := hx.1.1 _ _
  have hnn : ∀ i j, 0 ≤ x i j + (-α) * y i j := by
    intro i j
    by_cases h : (i, j) ∈ C
    · have := hmin _ h
      simp only [hydef, if_pos h]; simp only at this; linarith
    · simp only [hydef, if_neg h]; linarith [hx.1.1 i j]
  have hyz : ∀ i j, x i j = 0 → y i j = 0 := by
    intro i j h0
    simp only [hydef]
    rw [if_neg]
    intro hm
    have := hCs hm
    simp only [support, Finset.mem_filter] at this
    exact this.2 h0
  refine ⟨_, flow_add_dir G r x y hx hy.1.1.2 hy.1.2 (-α) hnn, ?_, ?_⟩
  · apply card_support_lt G x y hyz (-α) p1 (hCs hp1)
    simp only [hydef, if_pos (show (p1.1, p1.2) ∈ C from hp1)]
    ring
  · intro P
    exact ray G c hc P x y hx.1 hy α hα hnn

end SSHHAux



namespace SSHHAux

variable {n : ℕ}

noncomputable def sig {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n)
    (k : Fin (m + 2)) : ℝ :=
  if e k = (v k, v (k + 1)) then 1 else -1

noncomputable def dir {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n) :
    Fin n → Fin n → ℝ :=
  fun i j => ∑ k, if e k = (i, j) then sig v e k else 0

lemma dir_at {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n)
    (he : Function.Injective e) (k : Fin (m + 2)) : dir v e (e k).1 (e k).2 = sig v e k := by
  unfold dir
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    rw [if_neg]
    intro h
    exact hk' (he (by rw [h]))
  · simp

lemma dir_off {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n) (i j : Fin n)
    (h : ∀ k, e k ≠ (i, j)) : dir v e i j = 0 :=
  Finset.sum_eq_zero (fun k _ => if_neg (h k))

lemma sum_ind_snd {m : ℕ} (e : Fin (m + 2) → Fin n × Fin n) (s : ℝ) (k : Fin (m + 2)) (i : Fin n) :
    (∑ j, if e k = (j, i) then s else 0) = if (e k).2 = i then s else 0 := by
  have : ∀ j, (if e k = (j, i) then s else 0) =
      if (e k).1 = j then (if (e k).2 = i then s else 0) else 0 := by
    intro j
    by_cases h1 : (e k).1 = j <;> by_cases h2 : (e k).2 = i <;>
      simp [h1, h2, Prod.ext_iff, eq_comm]
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp

lemma sum_ind_fst {m : ℕ} (e : Fin (m + 2) → Fin n × Fin n) (s : ℝ) (k : Fin (m + 2)) (i : Fin n) :
    (∑ j, if e k = (i, j) then s else 0) = if (e k).1 = i then s else 0 := by
  have : ∀ j, (if e k = (i, j) then s else 0) =
      if (e k).2 = j then (if (e k).1 = i then s else 0) else 0 := by
    intro j
    by_cases h1 : (e k).1 = i <;> by_cases h2 : (e k).2 = j <;>
      simp [h1, h2, Prod.ext_iff, eq_comm]
  simp_rw [this]
  rw [Finset.sum_ite_eq]
  simp

lemma dir_bal (G : ArcGraph n) {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n)
    (hv : Function.Injective v)
    (hcyc : ∀ k, e k = (v k, v (k + 1)) ∨ e k = (v (k + 1), v k)) (hA : ∀ k, e k ∈ G.A) :
    ∀ i, (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), dir v e j i)
        - (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), dir v e i k) = 0 := by
  intro i
  have hoffA : ∀ a b, (a, b) ∉ G.A → dir v e a b = 0 :=
    fun a b h => dir_off v e a b (fun k hk => h (hk ▸ hA k))
  rw [Finset.sum_filter, Finset.sum_filter]
  have h1 : ∀ j, (if (j, i) ∈ G.A then dir v e j i else 0) = dir v e j i := by
    intro j; split_ifs with h
    · rfl
    · rw [hoffA _ _ h]
  have h2 : ∀ j, (if (i, j) ∈ G.A then dir v e i j else 0) = dir v e i j := by
    intro j; split_ifs with h
    · rfl
    · rw [hoffA _ _ h]
  simp_rw [h1, h2]
  unfold dir
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => if e y = (i, x) then sig v e y else 0)]
  simp_rw [sum_ind_snd, sum_ind_fst]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ k, ((if (e k).2 = i then sig v e k else 0) - if (e k).1 = i then sig v e k else 0)
      = (if v (k + 1) = i then (1:ℝ) else 0) - (if v k = i then 1 else 0) := by
    intro k
    rcases hcyc k with h | h
    · have hs : sig v e k = 1 := by simp [sig, h]
      rw [hs, h]
    · have hne : v k ≠ v (k + 1) := by
        intro h'
        have := hv h'
        have h1 : (1 : Fin (m + 2)) ≠ 0 := by
          intro h0
          have := congrArg Fin.val h0
          simp at this
        exact h1 (by
          have := congrArg (fun t => t - k) this
          simpa using this.symm)
      have hs : sig v e k = -1 := by
        simp only [sig]
        rw [if_neg]
        rw [h]; intro h''; exact hne (Prod.mk.inj h'').2
      rw [hs, h]
      simp only
      split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun k => rfl)

lemma mixed_case (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ) (hx : IsFlow G r x)
    {m : ℕ} (v : Fin (m + 2) → Fin n) (e : Fin (m + 2) → Fin n × Fin n)
    (hv : Function.Injective v) (he : Function.Injective e)
    (hcyc : ∀ k, e k ∈ support G x ∧ (e k = (v k, v (k + 1)) ∨ e k = (v (k + 1), v k)))
    (k1 k2 : Fin (m + 2)) (hk1 : e k1 = (v k1, v (k1 + 1))) (hk2 : e k2 ≠ (v k2, v (k2 + 1))) :
    ∃ x1, IsFlow G r x1 ∧ (support G x1).card < (support G x).card ∧
      flowCost G c x1 ≤ flowCost G c x := by
  classical
  set d := dir v e with hd
  have hsupp : ∀ k, x (e k).1 (e k).2 ≠ 0 ∧ (e k) ∈ G.A := by
    intro k
    have := (hcyc k).1
    simp only [support, Finset.mem_filter] at this
    exact ⟨this.2, this.1⟩
  set Fw := Finset.univ.filter (fun k => e k = (v k, v (k + 1)))
  set Bw := Finset.univ.filter (fun k => e k ≠ (v k, v (k + 1)))
  obtain ⟨a1, ha1, hmin1⟩ := Fw.exists_min_image (fun k => x (e k).1 (e k).2)
    ⟨k1, by simp [Fw, hk1]⟩
  obtain ⟨a2, ha2, hmin2⟩ := Bw.exists_min_image (fun k => x (e k).1 (e k).2)
    ⟨k2, by simp [Bw, hk2]⟩
  set α := x (e a1).1 (e a1).2
  set β := x (e a2).1 (e a2).2
  have hαpos : 0 < α := lt_of_le_of_ne (hx.1.1 _ _) (hsupp a1).1.symm
  have hβpos : 0 < β := lt_of_le_of_ne (hx.1.1 _ _) (hsupp a2).1.symm
  have hσ1 : sig v e a1 = 1 := by simp [Fw] at ha1; simp [sig, ha1]
  have hσ2 : sig v e a2 = -1 := by simp [Bw] at ha2; simp [sig, ha2]
  have hnn : ∀ t : ℝ, -α ≤ t → t ≤ β → ∀ i j, 0 ≤ x i j + t * d i j := by
    intro t ht1 ht2 i j
    by_cases hex : ∃ k, e k = (i, j)
    · obtain ⟨k, hk⟩ := hex
      have hi : i = (e k).1 := by rw [hk]
      have hj : j = (e k).2 := by rw [hk]
      subst hi hj
      rw [hd, dir_at v e he k]
      by_cases hf : e k = (v k, v (k + 1))
      · have := hmin1 k (by simp [Fw, hf])
        simp only [sig, if_pos hf]
        linarith
      · have := hmin2 k (by simp [Bw, hf])
        simp only [sig, if_neg hf]
        linarith
    · push Not at hex
      rw [hd, dir_off v e i j hex]
      linarith [hx.1.1 i j]
  have hdoff : ∀ i j, (i, j) ∉ G.A → d i j = 0 :=
    fun i j h => dir_off v e i j (fun k hk => h (hk ▸ (hsupp k).2))
  have hdbal := dir_bal G v e hv (fun k => (hcyc k).2) (fun k => (hsupp k).2)
  have hdz : ∀ i j, x i j = 0 → d i j = 0 := by
    intro i j h0
    apply dir_off v e i j
    intro k hk
    apply (hsupp k).1
    rw [hk]; exact h0
  have hf1 := flow_add_dir G r x d hx hdoff hdbal (-α) (hnn _ le_rfl (by linarith))
  have hf2 := flow_add_dir G r x d hx hdoff hdbal β (hnn _ (by linarith) le_rfl)
  have hcard1 := card_support_lt G x d hdz (-α) (e a1) (hcyc a1).1
    (by rw [hd, dir_at v e he a1, hσ1]; ring)
  have hcard2 := card_support_lt G x d hdz β (e a2) (hcyc a2).1
    (by rw [hd, dir_at v e he a2, hσ2]; ring)
  have hab : 0 < α + β := by linarith
  have h3 := three_point G c hc x (fun i j => x i j + (-α) * d i j) (fun i j => x i j + β * d i j)
    (hnn _ le_rfl (by linarith)) (hnn _ (by linarith) le_rfl) (β / (α + β)) (by positivity)
    (by rw [div_le_one hab]; linarith) (by intro i j; field_simp; ring)
  have hl0 : 0 ≤ β / (α + β) := by positivity
  have hl1 : 0 ≤ 1 - β / (α + β) := by rw [sub_nonneg, div_le_one hab]; linarith
  by_cases hle : flowCost G c (fun i j => x i j + (-α) * d i j) ≤
      flowCost G c (fun i j => x i j + β * d i j)
  · refine ⟨_, hf1, hcard1, ?_⟩
    have := mul_le_mul_of_nonneg_left hle hl1
    nlinarith
  · push Not at hle
    refine ⟨_, hf2, hcard2, ?_⟩
    have := mul_le_mul_of_nonneg_left hle.le hl0
    nlinarith

theorem reduce_to_extreme (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ) (hc : IsConcaveArcCost G c)
    (r : Fin n → ℝ) : ∀ x, IsFlow G r x → ∃ x', IsExtremeFlow G r x' ∧
      (RayNonneg G c → flowCost G c x' ≤ flowCost G c x) := by
  intro x
  induction h : (support G x).card using Nat.strong_induction_on generalizing x with
  | _ N ih =>
    intro hx
    by_cases hF : IsForest (support G x)
    · exact ⟨x, ⟨hx, hF⟩, fun _ => le_rfl⟩
    unfold IsForest at hF
    rw [not_not] at hF
    obtain ⟨m, v, e, hv, he, hcyc⟩ := hF
    have hsuppA : ∀ p ∈ support G x, p ∈ G.A := fun p hp => (Finset.mem_filter.1 hp).1
    have finish : ∀ x1, IsFlow G r x1 → (support G x1).card < (support G x).card →
        (RayNonneg G c → flowCost G c x1 ≤ flowCost G c x) →
        ∃ x', IsExtremeFlow G r x' ∧ (RayNonneg G c → flowCost G c x' ≤ flowCost G c x) := by
      intro x1 hx1 hlt hcost
      obtain ⟨x', hx', hc'⟩ := ih _ (h ▸ hlt) x1 rfl hx1
      exact ⟨x', hx', fun P => (hc' P).trans (hcost P)⟩
    by_cases hB : ∀ k, e k = (v k, v (k + 1))
    · have hCs : Finset.univ.image (fun k => (v k, v (k + 1))) ⊆ support G x := by
        intro p hp
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨k, rfl⟩ := hp
        rw [← hB k]; exact (hcyc k).1
      have hC : IsSimpleCircuit G (Finset.univ.image (fun k => (v k, v (k + 1)))) :=
        ⟨m, v, hv, fun k => hsuppA _ (hCs (Finset.mem_image_of_mem _ (Finset.mem_univ k))), rfl⟩
      obtain ⟨x1, hx1, hlt, hcost⟩ := directed_case G c hc r x hx _ hC hCs
      exact finish x1 hx1 hlt hcost
    by_cases hBw : ∀ k, e k ≠ (v k, v (k + 1))
    · have hB' : ∀ k, e k = (v (k + 1), v k) := fun k => ((hcyc k).2.resolve_left (hBw k))
      have hCs : Finset.univ.image (fun k => (v (k + 1), v k)) ⊆ support G x := by
        intro p hp
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
        obtain ⟨k, rfl⟩ := hp
        rw [← hB' k]; exact (hcyc k).1
      have hC := rev_circuit G v hv
        (fun k => hsuppA _ (hCs (Finset.mem_image_of_mem _ (Finset.mem_univ k))))
      obtain ⟨x1, hx1, hlt, hcost⟩ := directed_case G c hc r x hx _ hC hCs
      exact finish x1 hx1 hlt hcost
    push Not at hB hBw
    obtain ⟨k2, hk2⟩ := hB
    obtain ⟨k1, hk1⟩ := hBw
    obtain ⟨x1, hx1, hlt, hcost⟩ := mixed_case G c hc r x hx v e hv he hcyc k1 k2 hk1 hk2
    exact finish x1 hx1 hlt (fun _ => hcost)

end SSHHAux



namespace SSHHAux

variable {n : ℕ}

lemma cycle_split' {α : Type} [DecidableEq α] (l : List α) (h : ¬ l.Nodup) :
    ∃ p a q s, l = p ++ a :: (q ++ a :: s) ∧ (a :: q).Nodup := by
  induction l with
  | nil => simp at h
  | cons x t ih =>
    by_cases ht : t.Nodup
    · have hx : x ∈ t := by
        by_contra hx; exact h (List.nodup_cons.2 ⟨hx, ht⟩)
      obtain ⟨q, s, rfl⟩ := List.append_of_mem hx
      refine ⟨[], x, q, s, rfl, ?_⟩
      rw [List.nodup_append] at ht
      refine List.nodup_cons.2 ⟨fun hxq => ?_, ht.1⟩
      exact ht.2.2 x hxq x (List.mem_cons_self) rfl
    · obtain ⟨p, a, q, s, rfl, hn⟩ := ih ht
      exact ⟨x :: p, a, q, s, by simp, hn⟩

lemma cast_succ_fin' {m : ℕ} (k : ℕ) :
    (Nat.cast (k + 1) : Fin (m + 2)) = (Nat.cast k : Fin (m + 2)) + 1 := by
  push_cast; rfl

/-- A repeat-free list closing up into an `R`-chain, for irreflexive `R`, gives a cyclic
sequence of at least two distinct nodes. -/
lemma list_cycle_gen (R : Fin n → Fin n → Prop) (hR : ∀ a, ¬ R a a) (L : List (Fin n))
    (hL : L.Nodup) (hne : L ≠ []) (hch : List.IsChain R (L ++ [L.head hne])) :
    ∃ (m : ℕ) (v : Fin (m + 2) → Fin n), Function.Injective v ∧ ∀ k, R (v k) (v (k + 1)) := by
  have hlen : 2 ≤ L.length := by
    rcases L with _ | ⟨x, _ | ⟨y, t⟩⟩
    · exact absurd rfl hne
    · exfalso
      simp only [List.head_cons, List.cons_append, List.nil_append] at hch
      exact hR _ (List.isChain_pair.1 hch)
    · simp
  obtain ⟨m, hm⟩ : ∃ m, L.length = m + 2 := ⟨L.length - 2, by omega⟩
  let v : Fin (m + 2) → Fin n := fun k => L[k.val]'(by omega)
  have heq : L ++ [L.head hne] = (List.range (m + 3)).map (fun k : ℕ => v (Nat.cast k : Fin (m + 2))) := by
    apply List.ext_getElem
    · simp [hm]
    · intro i h1 h2
      simp only [List.getElem_map, v, Fin.val_natCast]
      rcases Nat.lt_or_ge i (m + 2) with hi | hi
      · rw [List.getElem_append_left (by omega)]
        congr 1; simp [Nat.mod_eq_of_lt hi]
      · have hi' : i = m + 2 := by simp [hm] at h1; omega
        rw [List.getElem_append_right (by omega)]
        simp only [List.getElem_singleton, List.head_eq_getElem]
        congr 1; subst hi'; simp
  refine ⟨m, v, ?_, ?_⟩
  · intro j j' h
    exact Fin.ext ((hL.getElem_inj_iff).1 h)
  · rw [heq, List.isChain_map] at hch
    have hch' : List.IsChain _ (List.range (m + 2).succ) := hch
    rw [List.isChain_range_succ] at hch'
    intro k
    have := hch' k.val k.isLt
    rwa [cast_succ_fin', Fin.cast_val_eq_self] at this

/-- A nonnegative "circulation" `z` with a positive entry has a cycle among its positive
entries. -/
lemma pos_cycle (z : Fin n → Fin n → ℝ) (hz : ∀ i j, 0 ≤ z i j) (hzz : ∀ a, z a a = 0)
    (hbal : ∀ i, ∑ j, z j i = ∑ j, z i j) (a0 b0 : Fin n) (h0 : 0 < z a0 b0) :
    ∃ (m : ℕ) (v : Fin (m + 2) → Fin n), Function.Injective v ∧
      ∀ k, 0 < z (v k) (v (k + 1)) := by
  classical
  have succ : ∀ a b, 0 < z a b → ∃ c, 0 < z b c := by
    intro a b hab
    by_contra hcon
    push Not at hcon
    have h1 : ∑ j, z b j ≤ 0 := Finset.sum_nonpos (fun j _ => hcon j)
    have h2 : z a b ≤ ∑ j, z j b :=
      Finset.single_le_sum (f := fun j => z j b) (fun j _ => hz j b) (Finset.mem_univ a)
    rw [hbal b] at h2
    linarith
  let T := {p : Fin n × Fin n // 0 < z p.1 p.2}
  let nxt : T → T := fun p => ⟨(p.1.2, Classical.choose (succ _ _ p.2)),
    Classical.choose_spec (succ _ _ p.2)⟩
  let f : ℕ → T := fun k => nxt^[k] ⟨(a0, b0), h0⟩
  have hf : ∀ k, f (k + 1) = nxt (f k) := fun k => Function.iterate_succ_apply' _ _ _
  let g : ℕ → Fin n := fun k => (f k).1.1
  have hg : ∀ k, 0 < z (g k) (g (k + 1)) := by
    intro k
    have : g (k + 1) = (f k).1.2 := by simp only [g, hf]; rfl
    rw [this]; exact (f k).2
  obtain ⟨i, j, hij, hgij⟩ := Finite.exists_ne_map_eq_of_infinite g
  wlog hlt : i < j generalizing i j
  · exact this j i (Ne.symm hij) hgij.symm (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hij))
  obtain ⟨N, rfl⟩ : ∃ N, j = i + (N + 1) := ⟨j - i - 1, by omega⟩
  set W := (List.range (N + 2)).map (fun t => g (i + t)) with hW
  have hWc : List.IsChain (fun a b => 0 < z a b) W := by
    rw [hW, List.isChain_map]
    show List.IsChain _ (List.range (N + 1).succ)
    rw [List.isChain_range_succ]
    intro t _
    have := hg (i + t)
    simpa [Nat.add_assoc] using this
  have hWn : ¬ W.Nodup := by
    intro hn
    have hlen : W.length = N + 2 := by simp [hW]
    have := (hn.getElem_inj_iff (i := 0) (j := N + 1) (hi := by omega) (hj := by omega)).1
      (by simp [hW, hgij])
    omega
  obtain ⟨p, a, q, s, hsplit, hnq⟩ := cycle_split' W hWn
  rw [hsplit] at hWc
  have h1 := List.isChain_split.1 hWc
  have h1' := List.isChain_split.1 (show List.IsChain (fun a b => 0 < z a b) ((a :: q) ++ a :: s)
    from by simpa using h1.2)
  have hch : List.IsChain (fun a b => 0 < z a b) ((a :: q) ++ [(a :: q).head (List.cons_ne_nil _ _)]) := by
    simpa using h1'.1
  exact list_cycle_gen (fun a b => 0 < z a b) (fun a h => by rw [hzz] at h; exact lt_irrefl _ h)
    (a :: q) hnq (List.cons_ne_nil _ _) hch

lemma filter_sum_eq (G : ArcGraph n) (d : Fin n → Fin n → ℝ) (hd : ∀ i j, (i, j) ∉ G.A → d i j = 0)
    (i : Fin n) :
    (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), d j i) = ∑ j, d j i ∧
    (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), d i k) = ∑ k, d i k := by
  constructor
  · rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro j _
    split_ifs with h
    · rfl
    · rw [hd _ _ h]
  · rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro j _
    split_ifs with h
    · rfl
    · rw [hd _ _ h]

/-- Two extreme flows for the same demand with the same support coincide. -/
lemma extreme_unique (G : ArcGraph n) (r : Fin n → ℝ) (x x' : Fin n → Fin n → ℝ)
    (hx : IsExtremeFlow G r x) (hx' : IsExtremeFlow G r x') (hs : support G x = support G x') :
    x = x' := by
  classical
  by_contra hne
  set d : Fin n → Fin n → ℝ := fun i j => x i j - x' i j with hd
  have hdoff : ∀ i j, (i, j) ∉ G.A → d i j = 0 := by
    intro i j h; simp [hd, hx.1.1.2 i j h, hx'.1.1.2 i j h]
  have hdbal : ∀ i, ∑ j, d j i = ∑ j, d i j := by
    intro i
    have e1 := hx.1.2 i
    have e2 := hx'.1.2 i
    obtain ⟨f1, f2⟩ := filter_sum_eq G d hdoff i
    rw [← f1, ← f2]
    simp only [hd, Finset.sum_sub_distrib]
    linarith
  have hdsupp : ∀ i j, d i j ≠ 0 → (i, j) ∈ support G x := by
    intro i j h
    have hA : (i, j) ∈ G.A := by
      by_contra hA; exact h (hdoff i j hA)
    by_contra hns
    have hx0 : x i j = 0 := by
      simp only [support, Finset.mem_filter, not_and, not_not] at hns; exact hns hA
    have : (i, j) ∉ support G x' := hs ▸ hns
    have hx'0 : x' i j = 0 := by
      simp only [support, Finset.mem_filter, not_and, not_not] at this; exact this hA
    exact h (by simp [hd, hx0, hx'0])
  obtain ⟨i0, j0, h0⟩ : ∃ i j, d i j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun i => funext fun j => sub_eq_zero.1 (hall i j))
  set z : Fin n → Fin n → ℝ := fun i j => max (d i j) 0 + max (-d j i) 0 with hz
  have hzn : ∀ i j, 0 ≤ z i j := fun i j => add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hzz : ∀ a, z a a = 0 := by
    intro a
    have : d a a = 0 := hdoff a a (fun h => G.loopless _ h rfl)
    simp [hz, this]
  have hzbal : ∀ i, ∑ j, z j i = ∑ j, z i j := by
    intro i
    have key : ∀ a : ℝ, max a 0 - max (-a) 0 = a := fun a => max_zero_sub_max_neg_zero_eq_self a
    have := hdbal i
    simp only [hz, Finset.sum_add_distrib]
    have e1 : ∑ j, max (d j i) 0 - ∑ j, max (-d j i) 0 = ∑ j, d j i := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _ => key _)
    have e2 : ∑ j, max (d i j) 0 - ∑ j, max (-d i j) 0 = ∑ j, d i j := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun j _ => key _)
    linarith
  obtain ⟨a0, b0, hab⟩ : ∃ a b, 0 < z a b := by
    rcases lt_or_gt_of_ne h0 with hl | hl
    · refine ⟨j0, i0, ?_⟩
      have : 0 < max (-d i0 j0) 0 := lt_max_of_lt_left (by linarith)
      linarith [le_max_right (d j0 i0) 0]
    · refine ⟨i0, j0, ?_⟩
      have : 0 < max (d i0 j0) 0 := lt_max_of_lt_left hl
      linarith [le_max_right (-d j0 i0) 0]
  obtain ⟨m, v, hv, hpos⟩ := pos_cycle z hzn hzz hzbal a0 b0 hab
  let e : Fin (m + 2) → Fin n × Fin n := fun k =>
    if 0 < d (v k) (v (k + 1)) then (v k, v (k + 1)) else (v (k + 1), v k)
  have hback : ∀ a b, ¬ 0 < d a b → 0 < z a b → d b a ≠ 0 := by
    intro a b h1 h2 h3
    have : max (d a b) 0 = 0 := max_eq_right (not_lt.1 h1)
    simp only [hz, this, h3, neg_zero, max_self, add_zero] at h2
    exact lt_irrefl _ h2
  apply hx.2
  refine ⟨m, v, e, hv, ?_, ?_⟩
  · intro k k' hkk
    simp only [e] at hkk
    split_ifs at hkk with h1 h2 h2
    · exact hv (Prod.mk.inj hkk).1
    · obtain ⟨ha, hb⟩ := Prod.mk.inj hkk
      exfalso
      have := hpos k'
      rw [← ha, ← hb] at h2 this
      -- h2 : ¬ 0 < d (v (k+1)) (v k), this : 0 < z (v (k+1)) (v k)
      simp only [hz] at this
      have m1 : max (d (v (k + 1)) (v k)) 0 = 0 := max_eq_right (not_lt.1 h2)
      have m2 : max (-d (v k) (v (k + 1))) 0 = 0 := max_eq_right (by linarith)
      rw [m1, m2] at this; norm_num at this
    · obtain ⟨ha, hb⟩ := Prod.mk.inj hkk
      exfalso
      have := hpos k
      rw [ha, hb] at h1 this
      simp only [hz] at this
      have m1 : max (d (v (k' + 1)) (v k')) 0 = 0 := max_eq_right (not_lt.1 h1)
      have m2 : max (-d (v k') (v (k' + 1))) 0 = 0 := max_eq_right (by linarith)
      rw [m1, m2] at this; norm_num at this
    · exact hv (Prod.mk.inj hkk).2
  · intro k
    simp only [e]
    split_ifs with h
    · exact ⟨hdsupp _ _ h.ne', Or.inl rfl⟩
    · exact ⟨hdsupp _ _ (hback _ _ h (hpos k)), Or.inr rfl⟩

lemma extreme_finite (G : ArcGraph n) (r : Fin n → ℝ) :
    {x : Fin n → Fin n → ℝ | IsExtremeFlow G r x}.Finite := by
  apply Set.Finite.of_finite_image (f := support G) (Set.toFinite _)
  intro x hx x' hx' h
  exact extreme_unique G r x x' hx hx' h

end SSHHAux



namespace SSHHAux

variable {n : ℕ}

lemma arc_scale (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {a k : ℝ}
    (ha : 0 ≤ a) (hk : 1 ≤ k) : f (k * a) ≤ k * f a := by
  have hk0 : 0 < k := by linarith
  have hka : (0:ℝ) ≤ k * a := by positivity
  have := hf.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hka)
    (show (0:ℝ) ≤ 1 - 1/k by rw [sub_nonneg]; exact (div_le_one hk0).2 hk)
    (show (0:ℝ) ≤ 1/k by positivity) (show (1 - 1/k) + 1/k = (1:ℝ) by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h0] at this
  have e : 1 / k * (k * a) = a := by field_simp
  rw [e] at this
  have := mul_le_mul_of_nonneg_left this hk0.le
  have e2 : k * (1 / k * f (k * a)) = f (k * a) := by field_simp
  linarith

lemma bounded_imp_nonneg (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsPreflow G y) (M : ℝ)
    (hM : ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => θ * y i j)) :
    ∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j) := by
  intro θ hθ
  by_contra hneg
  push Not at hneg
  set φ := flowCost G c (fun i j => θ * y i j) with hφ
  have hscale : ∀ k : ℝ, 1 ≤ k → flowCost G c (fun i j => (k * θ) * y i j) ≤ k * φ := by
    intro k hk
    unfold flowCost at hφ ⊢
    rw [hφ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    show c p.1 p.2 (k * θ * y p.1 p.2) ≤ k * c p.1 p.2 (θ * y p.1 p.2)
    rw [mul_assoc]
    exact arc_scale _ (hc p hp).1 (hc p hp).2 (mul_nonneg hθ (hy.1 _ _)) hk
  set k := max 1 (M / φ + 1)
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk2 : M / φ + 1 ≤ k := le_max_right _ _
  have h1 := hscale k hk1
  have h2 := hM (k * θ) (by positivity)
  have h3 : k * φ ≤ (M / φ + 1) * φ := mul_le_mul_of_nonpos_right hk2 hneg.le
  have hφne : φ ≠ 0 := hneg.ne
  have h4 : (M / φ + 1) * φ = M + φ := by field_simp
  linarith

theorem hh_proof (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (hflow : ∃ x, IsFlow G r x) :
    ((∃ x, IsMinCostFlow G c r x) ↔
      ∀ x, IsExtremeFlow G r x → ∀ y, IsSimpleCirculation G y →
        ∃ M : ℝ, ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => x i j + θ * y i j)) ∧
    ((∃ x, IsMinCostFlow G c r x) → ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x) := by
  have hred := reduce_to_extreme G c hc r
  have hfin := extreme_finite G r
  obtain ⟨x0, hx0⟩ := hflow
  obtain ⟨xe, hxe, -⟩ := hred x0 hx0
  have key : RayNonneg G c → ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x := by
    intro P
    obtain ⟨xs, hxs, hmin⟩ := Set.exists_min_image {x | IsExtremeFlow G r x} (flowCost G c)
      hfin ⟨xe, hxe⟩
    refine ⟨xs, ⟨hxs.1, fun x' hx' => ?_⟩, hxs⟩
    obtain ⟨x'', hx''e, hle⟩ := hred x' hx'
    exact (hmin x'' hx''e).trans (hle P)
  have toRay : (∀ x, IsExtremeFlow G r x → ∀ y, IsSimpleCirculation G y →
        ∃ M : ℝ, ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => x i j + θ * y i j)) →
      RayNonneg G c := by
    intro H y hy
    obtain ⟨M, hM⟩ := H xe hxe y hy
    apply bounded_imp_nonneg G c hc y hy.1.1 (M - flowCost G c xe)
    intro θ hθ
    have := (concave_sandwich G c hc xe y hxe.1.1 hy.1.1 θ hθ).2
    linarith [hM θ hθ]
  have fwd : (∃ x, IsMinCostFlow G c r x) →
      ∀ x, IsExtremeFlow G r x → ∀ y, IsSimpleCirculation G y →
        ∃ M : ℝ, ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => x i j + θ * y i j) := by
    rintro ⟨xm, hxm⟩ x hx y hy
    refine ⟨flowCost G c xm, fun θ hθ => hxm.2 _ ?_⟩
    have hnn : ∀ i j, 0 ≤ x i j + θ * y i j :=
      fun i j => add_nonneg (hx.1.1.1 i j) (mul_nonneg hθ (hy.1.1.1 i j))
    have hbal := hy.1.2
    exact flow_add_dir G r x y hx.1 hy.1.1.2 (fun i => by simpa using hbal i) θ hnn
  refine ⟨⟨fwd, fun H => ?_⟩, fun h => key (toRay (fwd h))⟩
  obtain ⟨x, hx, -⟩ := key (toRay H)
  exact ⟨x, hx⟩

end SSHHAux


theorem solution {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (r : Fin n → ℝ) (hflow : ∃ x, IsFlow G r x) :
    ((∃ x, IsMinCostFlow G c r x) ↔
      ∀ x, IsExtremeFlow G r x → ∀ y, IsSimpleCirculation G y →
        ∃ M : ℝ, ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => x i j + θ * y i j)) ∧
    ((∃ x, IsMinCostFlow G c r x) → ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x) :=
  SSHHAux.hh_proof G c hc r hflow
