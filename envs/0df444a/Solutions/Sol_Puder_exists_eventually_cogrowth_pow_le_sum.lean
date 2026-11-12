-- Prove2me | solution 1 for Puder.exists_eventually_cogrowth_pow_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:27:41.607177+00:00
-- url     : https://prove2.me/submissions/82247496-7a00-4830-8d95-801459dc9ac6

import Mathlib
import Definitions.Def_StrongConv

open Filter

namespace Puder.Q263Cog

variable {k : ℕ}

/-- The generator attached to a letter. -/
def gen : Fin k ⊕ Fin k → FreeGroup (Fin k)
  | Sum.inl i => FreeGroup.of i
  | Sum.inr i => (FreeGroup.of i)⁻¹

/-- The free-group letter attached to a letter. -/
def toPair : Fin k ⊕ Fin k → Fin k × Bool
  | Sum.inl i => (i, true)
  | Sum.inr i => (i, false)

theorem gen_swap (a : Fin k ⊕ Fin k) : gen a.swap = (gen a)⁻¹ := by
  cases a <;> simp [gen]

theorem gen_eq_mk (a : Fin k ⊕ Fin k) : gen a = FreeGroup.mk [toPair a] := by
  cases a <;> simp [gen, toPair, FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]

theorem prod_eq_mk (w : List (Fin k ⊕ Fin k)) : (w.map gen).prod = FreeGroup.mk (w.map toPair) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, ih, gen_eq_mk, FreeGroup.mul_mk]
    rfl

theorem toPair_injective : Function.Injective (toPair (k := k)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [toPair]

/-- Reduced letter lists: no letter followed by its inverse. -/
def Red (w : List (Fin k ⊕ Fin k)) : Prop := w.IsChain fun a b => b ≠ a.swap

theorem isReduced_map {w : List (Fin k ⊕ Fin k)} (h : Red w) :
    FreeGroup.IsReduced (w.map toPair) := by
  unfold Red at h
  unfold FreeGroup.IsReduced
  rw [List.isChain_map]
  refine h.imp ?_
  intro a b hab h1
  cases a <;> cases b <;> simp_all [toPair, Sum.swap]

theorem toWord_prod {w : List (Fin k ⊕ Fin k)} (h : Red w) :
    (w.map gen).prod.toWord = w.map toPair := by
  rw [prod_eq_mk, FreeGroup.toWord_mk, (isReduced_map h).reduce_eq]

/-- The word of a letter sequence. -/
def wd {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) : FreeGroup (Fin k) := ((List.ofFn i).map gen).prod

theorem wordFree_eq {t : ℕ} (i : Fin t → Fin k ⊕ Fin k) :
    StrongConv.wordFree (List.ofFn fun j => some (i j)) = wd i := by
  unfold StrongConv.wordFree wd
  rw [show (List.ofFn fun j => some (i j)) = (List.ofFn i).map some from List.map_ofFn.symm,
    List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

/-- Number of letter sequences of length `t` with word `g`. -/
noncomputable def N (k t : ℕ) (g : FreeGroup (Fin k)) : ℝ :=
  ∑ i : Fin t → Fin k ⊕ Fin k, if wd i = g then 1 else 0

theorem N_nonneg (t : ℕ) (g : FreeGroup (Fin k)) : 0 ≤ N k t g := by
  unfold N
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem wd_cons {t : ℕ} (x : Fin k ⊕ Fin k) (i : Fin t → Fin k ⊕ Fin k) :
    wd (Fin.cons x i : Fin (t + 1) → Fin k ⊕ Fin k) = gen x * wd i := by
  simp [wd, List.ofFn_succ]

theorem N_succ (t : ℕ) (g : FreeGroup (Fin k)) :
    N k (t + 1) g = ∑ x, N k t ((gen x)⁻¹ * g) := by
  unfold N
  rw [← (Fin.consEquiv fun _ => Fin k ⊕ Fin k).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show (Fin.consEquiv fun _ => Fin k ⊕ Fin k) (x, i) = Fin.cons x i from rfl, wd_cons]
  simp only [eq_inv_mul_iff_mul_eq]

/-- Weighted count of height paths from `0` staying `≥ 1` afterwards: weight `q` per down step. -/
def a (q : ℝ) : ℕ → ℕ → ℝ
  | 0, h => if h = 0 then 1 else 0
  | _ + 1, 0 => 0
  | t + 1, h + 1 => a q t h + q * a q t (h + 2)

theorem a_nonneg {q : ℝ} (hq : 0 ≤ q) : ∀ t h, 0 ≤ a q t h
  | 0, h => by unfold a; split_ifs <;> norm_num
  | t + 1, 0 => by simp [a]
  | t + 1, h + 1 => by
    simp only [a]
    have := a_nonneg hq t h
    have := a_nonneg hq t (h + 2)
    positivity

theorem a_zero_of_lt (q : ℝ) : ∀ t h, t < h → a q t h = 0
  | 0, h, hh => by simp [a]; omega
  | t + 1, 0, hh => by simp [a]
  | t + 1, h + 1, hh => by
    simp only [a]
    rw [a_zero_of_lt q t h (by omega), a_zero_of_lt q t (h + 2) (by omega)]
    ring

theorem a_self (q : ℝ) : ∀ t, a q t t = 1
  | 0 => by simp [a]
  | t + 1 => by
    simp only [a]
    rw [a_self q t, a_zero_of_lt q t (t + 2) (by omega)]
    ring

theorem N_ge (hk : 1 ≤ k) : ∀ (t : ℕ) (w : List (Fin k ⊕ Fin k)), Red w →
    a (2 * k - 1) t w.length ≤ N k t (w.map gen).prod
  | 0, w, _ => by
    unfold a N
    split_ifs with h
    · rw [List.length_eq_zero_iff] at h
      subst h
      rw [Finset.sum_eq_single (fun j : Fin 0 => (j.elim0 : Fin k ⊕ Fin k))]
      · simp [wd]
      · intro b _ hb
        exact absurd (funext fun j => j.elim0) hb
      · intro h; exact absurd (Finset.mem_univ _) h
    · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  | t + 1, [], _ => by
    simp only [List.length_nil, a]
    exact N_nonneg _ _
  | t + 1, y :: w, hw => by
    simp only [List.length_cons, a]
    rw [N_succ, ← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
    have hw' : Red w := hw.tail
    have h1 : a (2 * k - 1) t w.length ≤ N k t ((gen y)⁻¹ * ((y :: w).map gen).prod) := by
      rw [List.map_cons, List.prod_cons, inv_mul_cancel_left]
      exact N_ge hk t w hw'
    have h2 : ∀ x ∈ Finset.univ.erase y,
        a (2 * k - 1) t (w.length + 2) ≤ N k t ((gen x)⁻¹ * ((y :: w).map gen).prod) := by
      intro x hx
      have hxy : x ≠ y := Finset.ne_of_mem_erase hx
      have := N_ge hk t (x.swap :: y :: w) (by
        unfold Red
        rw [List.isChain_cons_cons]
        refine ⟨?_, hw⟩
        rw [Sum.swap_swap]
        exact fun h => hxy h.symm)
      simpa [gen_swap] using this
    have h3 := Finset.card_nsmul_le_sum _ _ _ h2
    have hc : ((Finset.univ.erase y).card : ℝ) = 2 * k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ, Fintype.card_sum,
        Fintype.card_fin]
      push_cast [show 1 ≤ k + k by omega]
      ring
    rw [nsmul_eq_mul, hc] at h3
    linarith

/-! ## Weighted path counts -/

section Analytic

variable (q α : ℝ) (R : ℕ)

/-- `a` weighted by `α ^ height`. -/
noncomputable def b (t h : ℕ) : ℝ := a q t h * α ^ h

/-- The harmonic-type potential `1 - ρ ^ (h + 1 - R)` above `R`, with `ρ = q / α ^ 2`. -/
noncomputable def φ (h : ℕ) : ℝ := if R ≤ h then 1 - (q / α ^ 2) ^ (h + 1 - R) else 0

noncomputable def S (t M : ℕ) : ℝ := ∑ h ∈ Finset.range M, b q α t h * φ q α R h

variable {q α R}

theorem b_succ (hα : 0 < α) (t h : ℕ) :
    b q α (t + 1) (h + 1) = α * b q α t h + q / α * b q α t (h + 2) := by
  simp only [b, a]
  field_simp
  ring

theorem b_succ_zero (t : ℕ) : b q α (t + 1) 0 = 0 := by simp [b, a]

theorem b_nonneg (hq : 0 ≤ q) (hα : 0 < α) (t h : ℕ) : 0 ≤ b q α t h :=
  mul_nonneg (a_nonneg hq t h) (by positivity)

theorem b_zero_of_lt (t h : ℕ) (hh : t < h) : b q α t h = 0 := by
  simp [b, a_zero_of_lt q t h hh]

theorem rho_nonneg (hq : 0 ≤ q) : 0 ≤ q / α ^ 2 := by positivity

theorem rho_lt_one (hα : 0 < α) (hqα : q < α ^ 2) : q / α ^ 2 < 1 := by
  rw [div_lt_one (by positivity)]; exact hqα

theorem φ_zero (hR : 1 ≤ R) : φ q α R 0 = 0 := by
  simp [φ]; omega

theorem φ_nonneg (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) (h : ℕ) : 0 ≤ φ q α R h := by
  unfold φ
  split_ifs
  · have := pow_le_one₀ (n := h + 1 - R) (rho_nonneg (α := α) hq) (rho_lt_one hα hqα).le
    linarith
  · exact le_refl _

theorem φ_le_one (hq : 0 ≤ q) (h : ℕ) : φ q α R h ≤ if R ≤ h then 1 else 0 := by
  unfold φ
  split_ifs
  · have := pow_nonneg (rho_nonneg (α := α) hq) (h + 1 - R)
    linarith
  · exact le_refl _

theorem φ_key (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) (hR : 1 ≤ R) (h : ℕ) :
    (α + q / α) * φ q α R h ≤ α * φ q α R (h + 1) + q / α * φ q α R (h - 1) := by
  by_cases hh : R ≤ h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hh
    have e1 : φ q α R (R + n) = 1 - (q / α ^ 2) ^ (n + 1) := by
      simp only [φ, if_pos hh]; congr 2; omega
    have e2 : φ q α R (R + n + 1) = 1 - (q / α ^ 2) ^ (n + 2) := by
      simp only [φ, if_pos (show R ≤ R + n + 1 by omega)]; congr 2; omega
    have e3 : φ q α R (R + n - 1) = 1 - (q / α ^ 2) ^ n := by
      unfold φ
      split_ifs with h3
      · congr 2; omega
      · have : n = 0 := by omega
        subst this; simp
    rw [e1, e2, e3]
    apply le_of_eq
    have hq' : q = q / α ^ 2 * α ^ 2 := by field_simp
    generalize q / α ^ 2 = ρ at hq' ⊢
    subst hq'
    field_simp
    ring
  · have h0 : φ q α R h = 0 := by simp [φ, hh]
    rw [h0, mul_zero]
    have := φ_nonneg (R := R) hq hα hqα (h + 1)
    have := φ_nonneg (R := R) hq hα hqα (h - 1)
    have : 0 ≤ q / α := by positivity
    positivity

theorem shift_sum (hR : 1 ≤ R) (t m : ℕ) (hm : t ≤ m) :
    ∑ h ∈ Finset.range (m + 1), b q α t (h + 2) * φ q α R (h + 1) =
      ∑ h ∈ Finset.range (m + 1), b q α t h * φ q α R (h - 1) := by
  have e1 : ∑ h ∈ Finset.range (m + 3), b q α t h * φ q α R (h - 1) =
      ∑ h ∈ Finset.range (m + 1), b q α t (h + 2) * φ q α R (h + 1) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp [φ_zero hR]
  have e2 : ∑ h ∈ Finset.range (m + 3), b q α t h * φ q α R (h - 1) =
      ∑ h ∈ Finset.range (m + 1), b q α t h * φ q α R (h - 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, b_zero_of_lt t (m + 1) (by omega),
      b_zero_of_lt t (m + 1 + 1) (by omega)]
    ring
  rw [← e1, e2]

theorem S_step (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) (hR : 1 ≤ R) (t m : ℕ)
    (hm : t ≤ m) : (α + q / α) * S q α R t (m + 1) ≤ S q α R (t + 1) (m + 2) := by
  unfold S
  rw [Finset.sum_range_succ' _ (m + 1), b_succ_zero, zero_mul, add_zero]
  simp_rw [b_succ hα, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    shift_sum hR t m hm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have := φ_key (R := R) hq hα hqα hR h
  have := b_nonneg hq hα t h
  nlinarith

/-- `Φ t = S t (t + 1)`. -/
theorem S_iter (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) (hR : 1 ≤ R) :
    ∀ n : ℕ, (α + q / α) ^ n * S q α R R (R + 1) ≤ S q α R (R + n) (R + n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := S_iter hq hα hqα hR n
    have hs := S_step hq hα hqα hR (R + n) (R + n) le_rfl
    have hl : 0 ≤ α + q / α := by positivity
    rw [show R + (n + 1) = R + n + 1 by omega, show R + n + 1 + 1 = R + n + 2 by omega, pow_succ]
    calc (α + q / α) ^ n * (α + q / α) * S q α R R (R + 1)
        = (α + q / α) * ((α + q / α) ^ n * S q α R R (R + 1)) := by ring
      _ ≤ (α + q / α) * S q α R (R + n) (R + n + 1) := mul_le_mul_of_nonneg_left ih hl
      _ ≤ _ := hs

theorem S_base (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) :
    α ^ R * (1 - q / α ^ 2) ≤ S q α R R (R + 1) := by
  unfold S
  have : b q α R R * φ q α R R = α ^ R * (1 - q / α ^ 2) := by
    simp [b, φ, a_self]
  rw [← this]
  exact Finset.single_le_sum (f := fun h => b q α R h * φ q α R h)
    (fun h _ => mul_nonneg (b_nonneg hq hα R h) (φ_nonneg hq hα hqα h))
    (Finset.self_mem_range_succ R)

theorem S_le (hq : 0 ≤ q) (hα : 0 < α) (t M : ℕ) :
    S q α R t M ≤ ∑ h ∈ Finset.range M with R ≤ h, a q t h * α ^ h := by
  unfold S
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro h _
  have h1 := φ_le_one (α := α) (R := R) hq h
  have h2 := b_nonneg hq hα t h
  unfold b at h2 ⊢
  split_ifs at h1 ⊢ <;> nlinarith

theorem analytic (hq : 0 ≤ q) (hα : 0 < α) (hqα : q < α ^ 2) (hR : 1 ≤ R) (t : ℕ) (ht : R ≤ t) :
    α ^ R * (1 - q / α ^ 2) * (α + q / α) ^ (t - R) ≤
      ∑ h ∈ Finset.range (t + 1) with R ≤ h, a q t h * α ^ h := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [show R + n - R = n by omega]
  refine le_trans ?_ (S_le hq hα _ _)
  refine le_trans ?_ (S_iter hq hα hqα hR n)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (S_base hq hα hqα) (by positivity)

end Analytic

/-! ## Combining -/

theorem N_mul (t : ℕ) (f : FreeGroup (Fin k) → ℝ) (g : FreeGroup (Fin k)) :
    N k t g * f g = ∑ i : Fin t → Fin k ⊕ Fin k with wd i = g, f (wd i) := by
  unfold N
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [h, one_mul]
  · rw [zero_mul]

theorem per_r (hk : 1 ≤ k) (f : FreeGroup (Fin k) → ℝ) (hf : ∀ g, 0 ≤ f g) (t r : ℕ) :
    a (2 * k - 1) t r * ∑ j : Fin r → Fin k ⊕ Fin k with
        (∀ (m : Fin r) (hm : (m : ℕ) + 1 < r), j ⟨m + 1, hm⟩ ≠ (j m).swap), f (wd j) ≤
      ∑ i : Fin t → Fin k ⊕ Fin k with (wd i).toWord.length = r, f (wd i) := by
  set NB := (Finset.univ : Finset (Fin r → Fin k ⊕ Fin k)).filter
    (fun j => ∀ (m : Fin r) (hm : (m : ℕ) + 1 < r), j ⟨m + 1, hm⟩ ≠ (j m).swap) with hNB
  have hred : ∀ j ∈ NB, Red (List.ofFn j) := by
    intro j hj
    rw [hNB, Finset.mem_filter] at hj
    unfold Red
    rw [List.isChain_ofFn]
    intro m hm
    exact hj.2 ⟨m, by omega⟩ hm
  have hword : ∀ j ∈ NB, (wd j).toWord = (List.ofFn j).map toPair := fun j hj =>
    toWord_prod (hred j hj)
  have hinj : Set.InjOn wd (NB : Set (Fin r → Fin k ⊕ Fin k)) := by
    intro j hj j' hj' h
    have := congrArg FreeGroup.toWord h
    rw [hword j hj, hword j' hj'] at this
    exact List.ofFn_injective ((List.map_injective_iff.mpr toPair_injective) this)
  set S := NB.image wd with hS
  calc a (2 * k - 1) t r * ∑ j ∈ NB, f (wd j)
      = ∑ g ∈ S, a (2 * k - 1) t r * f g := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ ∑ g ∈ S, N k t g * f g := by
        apply Finset.sum_le_sum
        intro g hg
        rw [hS, Finset.mem_image] at hg
        obtain ⟨j, hj, rfl⟩ := hg
        apply mul_le_mul_of_nonneg_right _ (hf _)
        have := N_ge hk t (List.ofFn j) (hred j hj)
        rwa [List.length_ofFn] at this
    _ = ∑ i : Fin t → Fin k ⊕ Fin k with wd i ∈ S, f (wd i) := by
        simp_rw [N_mul]
        exact Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          rw [hS, Finset.mem_image] at hi
          obtain ⟨j, hj, hji⟩ := hi
          rw [← hji, hword j hj, List.length_map, List.length_ofFn]
        · intro i _ _
          exact hf _

theorem beta_ge (hk : 1 ≤ k) (f : FreeGroup (Fin k) → ℝ) (hf : ∀ g, 0 ≤ f g) (t : ℕ)
    (s : Finset ℕ) :
    ∑ r ∈ s, a (2 * k - 1) t r * ∑ j : Fin r → Fin k ⊕ Fin k with
        (∀ (m : Fin r) (hm : (m : ℕ) + 1 < r), j ⟨m + 1, hm⟩ ≠ (j m).swap), f (wd j) ≤
      ∑ i : Fin t → Fin k ⊕ Fin k, f (wd i) := by
  calc _ ≤ ∑ r ∈ s, ∑ i : Fin t → Fin k ⊕ Fin k with (wd i).toWord.length = r, f (wd i) :=
        Finset.sum_le_sum fun r _ => per_r hk f hf t r
    _ = ∑ i : Fin t → Fin k ⊕ Fin k with (wd i).toWord.length ∈ s, f (wd i) :=
        Finset.sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hf _)

end Puder.Q263Cog

namespace Puder

open Q263Cog in
theorem exists_eventually_cogrowth_pow_le_sum_dev (k : ℕ) (hk : 2 ≤ k) (f : FreeGroup (Fin k) → ℝ)
    (hf : ∀ g, 0 ≤ f g) (α c : ℝ) (hα : Real.sqrt (2 * k - 1) < α) (hc : 0 < c)
    (hν : ∀ᶠ t : ℕ in atTop, c * α ^ t ≤ ∑ i : Fin t → Fin k ⊕ Fin k with
        (∀ (j : Fin t) (hj : (j : ℕ) + 1 < t), i ⟨j + 1, hj⟩ ≠ (i j).swap),
        f (StrongConv.wordFree (List.ofFn fun j => some (i j)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℕ in atTop,
      C * ((2 * k - 1) / α + α) ^ t ≤ ∑ i : Fin t → Fin k ⊕ Fin k, f (StrongConv.wordFree (List.ofFn fun j => some (i j))) := by
  simp_rw [wordFree_eq] at hν ⊢
  set q : ℝ := 2 * k - 1 with hqdef
  have hq : 0 ≤ q := by
    rw [hqdef]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hα0 : 0 < α := lt_of_le_of_lt (Real.sqrt_nonneg _) hα
  have hqα : q < α ^ 2 := (Real.sqrt_lt' hα0).mp hα
  obtain ⟨R0, hR0⟩ := eventually_atTop.mp hν
  set R := max R0 1 with hRdef
  have hR : 1 ≤ R := le_max_right _ _
  set lam := α + q / α with hlam
  have hlam0 : 0 < lam := by positivity
  have hρ : 0 < 1 - q / α ^ 2 := by
    have := rho_lt_one hα0 hqα
    linarith
  refine ⟨c * (α ^ R * (1 - q / α ^ 2)) / lam ^ R, by positivity, ?_⟩
  rw [eventually_atTop]
  refine ⟨R, fun t ht => ?_⟩
  rw [show q / α + α = lam by rw [hlam]; ring]
  have hpow : lam ^ t = lam ^ R * lam ^ (t - R) := by
    rw [← pow_add]; congr 1; omega
  have hA := analytic hq hα0 hqα hR t ht
  have hB := beta_ge (by omega) f hf t ((Finset.range (t + 1)).filter (R ≤ ·))
  calc c * (α ^ R * (1 - q / α ^ 2)) / lam ^ R * lam ^ t
      = c * (α ^ R * (1 - q / α ^ 2) * lam ^ (t - R)) := by
        rw [hpow]; field_simp
    _ ≤ c * ∑ h ∈ Finset.range (t + 1) with R ≤ h, a q t h * α ^ h :=
        mul_le_mul_of_nonneg_left hA hc.le
    _ = ∑ h ∈ Finset.range (t + 1) with R ≤ h, a q t h * (c * α ^ h) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun h _ => by ring
    _ ≤ _ := by
        refine Finset.sum_le_sum fun h hh => ?_
        rw [Finset.mem_filter] at hh
        exact mul_le_mul_of_nonneg_left (hR0 h (le_trans (le_max_left _ _) hh.2))
          (a_nonneg hq t h)
    _ ≤ _ := hB

end Puder

theorem solution : type_of% @Puder.exists_eventually_cogrowth_pow_le_sum_dev := @Puder.exists_eventually_cogrowth_pow_le_sum_dev
