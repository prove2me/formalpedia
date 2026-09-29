-- Prove2me | solution 2 for buchholz_evenq_trace_pairbound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T21:40:17.960611+00:00
-- url     : https://prove2.me/submissions/50dc4452-6c17-4fe2-a6ef-7c555adf5fec

import Mathlib
import Definitions.Def_buchholz_pairing
import Definitions.Def_matrix_completion_gram_schatten

set_option autoImplicit false

open Finset MatrixCompletion

namespace SolE8b03350


def extF {V : Type*} (d : V) {N : ℕ} (s : Fin N → V) (i : ℕ) : V :=
  if h : i < N then s ⟨i, h⟩ else d

lemma extF_snoc_lt {V : Type*} (d : V) {N : ℕ} (s : Fin (N+1) → V) (y : V) (i : ℕ)
    (hi : i < N + 1) :
    extF d (Fin.snoc s y : Fin (N+2) → V) i = extF d s i := by
  unfold extF
  rw [dif_pos (by omega), dif_pos hi]
  have : (⟨i, by omega⟩ : Fin (N+2)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

lemma extF_snoc_last {V : Type*} (d : V) {N : ℕ} (s : Fin (N+1) → V) (y : V) :
    extF d (Fin.snoc s y : Fin (N+2) → V) (N+1) = y := by
  unfold extF
  rw [dif_pos (by omega)]
  have : (⟨N+1, by omega⟩ : Fin (N+2)) = Fin.last (N+1) := rfl
  rw [this, Fin.snoc_last]

theorem chain_bound {V : Type*} [Fintype V] (d : V) (Z ρ : V → ℝ) (par : ℕ → ℕ)
    (Kt : ℕ → V → V → ℝ)
    (hpar : ∀ m, par m ≤ m)
    (hK0 : ∀ m x y, 0 ≤ Kt m x y) (hKsub : ∀ m x, ∑ y, Kt m x y ≤ 1)
    (hKinv : ∀ m y, ∑ x, Z x * Kt m x y ≤ Z y)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : ∀ x, ρ x ≤ Z x) :
    ∀ (N : ℕ) (g : V → ℝ), (∀ x, 0 ≤ g x) → ∀ tstar ≤ N,
    ∑ s : Fin (N+1) → V, ρ (extF d s 0) *
        (∏ m ∈ range N, Kt m (extF d s (par m)) (extF d s (m+1))) * g (extF d s tstar)
      ≤ ∑ x, Z x * g x := by
  intro N
  induction N with
  | zero =>
    intro g hg tstar ht
    have ht0 : tstar = 0 := by omega
    subst ht0
    simp only [range_zero, prod_empty, mul_one]
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    apply sum_le_sum
    intro x _
    simp only [extF, Equiv.funUnique_symm_apply]
    simp
    exact mul_le_mul_of_nonneg_right (hρ x) (hg x)
  | succ N ih =>
    intro g hg tstar ht
    have key : ∀ (s' : Fin (N+1) → V) (y : V),
        ρ (extF d (Fin.snoc s' y : Fin (N+2) → V) 0) *
          (∏ m ∈ range (N+1), Kt m (extF d (Fin.snoc s' y : Fin (N+2) → V) (par m))
              (extF d (Fin.snoc s' y : Fin (N+2) → V) (m+1))) =
        (ρ (extF d s' 0) * (∏ m ∈ range N, Kt m (extF d s' (par m)) (extF d s' (m+1)))) *
          Kt N (extF d s' (par N)) y := by
      intro s' y
      rw [prod_range_succ, extF_snoc_lt d s' y 0 (by omega), extF_snoc_last,
        extF_snoc_lt d s' y (par N) (by have := hpar N; omega)]
      rw [prod_congr rfl (fun m hm => by
        have hm' := mem_range.mp hm
        rw [extF_snoc_lt d s' y (par m) (by have := hpar m; omega),
          extF_snoc_lt d s' y (m+1) (by omega)])]
      ring
    have hA : ∀ s' : Fin (N+1) → V,
        0 ≤ ρ (extF d s' 0) * (∏ m ∈ range N, Kt m (extF d s' (par m)) (extF d s' (m+1))) := by
      intro s'
      exact mul_nonneg (hρ0 _) (prod_nonneg fun m _ => hK0 _ _ _)
    rw [← (Fin.snocEquiv (fun _ => V)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    simp only [show ∀ p : V × (Fin (N+1) → V), (Fin.snocEquiv (fun _ => V)) p = Fin.snoc p.2 p.1
      from fun p => rfl]
    rcases Nat.lt_or_ge tstar (N+1) with hts | hts
    · refine le_trans (sum_le_sum fun s' _ => ?_) (ih g hg tstar (by omega))
      have e1 : ∀ y, ρ (extF d (Fin.snoc s' y : Fin (N+2) → V) 0) *
          (∏ m ∈ range (N+1), Kt m (extF d (Fin.snoc s' y : Fin (N+2) → V) (par m))
              (extF d (Fin.snoc s' y : Fin (N+2) → V) (m+1))) *
            g (extF d (Fin.snoc s' y : Fin (N+2) → V) tstar)
          = (ρ (extF d s' 0) * (∏ m ∈ range N, Kt m (extF d s' (par m)) (extF d s' (m+1)))) *
              g (extF d s' tstar) * Kt N (extF d s' (par N)) y := by
        intro y
        rw [key, extF_snoc_lt d s' y tstar hts]
        ring
      rw [sum_congr rfl (fun y _ => e1 y), ← mul_sum]
      calc _ ≤ (ρ (extF d s' 0) * (∏ m ∈ range N, Kt m (extF d s' (par m)) (extF d s' (m+1)))) *
              g (extF d s' tstar) * 1 := by
            gcongr
            · exact mul_nonneg (hA s') (hg _)
            · exact hKsub _ _
        _ = _ := by ring
    · have htN : tstar = N + 1 := by omega
      subst htN
      set g' : V → ℝ := fun x => ∑ y, Kt N x y * g y with hg'
      have hg'0 : ∀ x, 0 ≤ g' x := fun x => sum_nonneg fun y _ => mul_nonneg (hK0 _ _ _) (hg y)
      have e1 : ∀ s' : Fin (N+1) → V, ∑ y, ρ (extF d (Fin.snoc s' y : Fin (N+2) → V) 0) *
          (∏ m ∈ range (N+1), Kt m (extF d (Fin.snoc s' y : Fin (N+2) → V) (par m))
              (extF d (Fin.snoc s' y : Fin (N+2) → V) (m+1))) *
            g (extF d (Fin.snoc s' y : Fin (N+2) → V) (N+1))
          = (ρ (extF d s' 0) * (∏ m ∈ range N, Kt m (extF d s' (par m)) (extF d s' (m+1)))) *
              g' (extF d s' (par N)) := by
        intro s'
        rw [hg', mul_sum]
        apply sum_congr rfl
        intro y _
        rw [key, extF_snoc_last]
        ring
      rw [sum_congr rfl (fun s' _ => e1 s')]
      refine le_trans (ih g' hg'0 (par N) (hpar N)) ?_
      calc ∑ x, Z x * g' x = ∑ y, (∑ x, Z x * Kt N x y) * g y := by
            rw [hg']
            simp only [mul_sum, sum_mul]
            rw [Finset.sum_comm]
            apply sum_congr rfl; intro y _; apply sum_congr rfl; intro x _; ring
        _ ≤ ∑ y, Z y * g y := by
            apply sum_le_sum; intro y _
            exact mul_le_mul_of_nonneg_right (hKinv N y) (hg y)



theorem exists_pairing {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ S : Finset α, (∀ c, Even (S.filter (fun x => f x = c)).card) →
    ∃ g : α → α, Function.Involutive g ∧ (∀ x ∈ S, g x ≠ x ∧ f (g x) = f x) ∧
      (∀ x ∉ S, g x = x) := by
  suffices H : ∀ k, ∀ S : Finset α, S.card = k → (∀ c, Even (S.filter (fun x => f x = c)).card) →
      ∃ g : α → α, Function.Involutive g ∧ (∀ x ∈ S, g x ≠ x ∧ f (g x) = f x) ∧
        (∀ x ∉ S, g x = x) from fun S => H _ S rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S hS heven
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · exact ⟨id, fun _ => rfl, by simp [h], fun _ _ => rfl⟩
  have hfib : x ∈ S.filter (fun z => f z = f x) := mem_filter.mpr ⟨hx, rfl⟩
  have hcard : 2 ≤ (S.filter (fun z => f z = f x)).card := by
    have h1 := card_pos.mpr ⟨x, hfib⟩
    obtain ⟨r, hr⟩ := heven (f x)
    omega
  obtain ⟨y, hy⟩ : ((S.filter (fun z => f z = f x)).erase x).Nonempty := by
    rw [← card_pos, card_erase_of_mem hfib]; omega
  have hyx : y ≠ x := ne_of_mem_erase hy
  have hyS : y ∈ S := (mem_filter.mp (mem_of_mem_erase hy)).1
  have hfy : f y = f x := (mem_filter.mp (mem_of_mem_erase hy)).2
  have hS'card : ((S.erase x).erase y).card = k - 2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨hyx, hyS⟩), card_erase_of_mem hx]; omega
  have heven' : ∀ c, Even (((S.erase x).erase y).filter (fun z => f z = c)).card := by
    intro c
    rw [filter_erase, filter_erase]
    by_cases hc : f x = c
    · have hxm : x ∈ S.filter (fun z => f z = c) := mem_filter.mpr ⟨hx, hc⟩
      have hym : y ∈ (S.filter (fun z => f z = c)).erase x :=
        mem_erase.mpr ⟨hyx, mem_filter.mpr ⟨hyS, hfy.trans hc⟩⟩
      rw [card_erase_of_mem hym, card_erase_of_mem hxm]
      have h2 : 2 ≤ (S.filter (fun z => f z = c)).card := by
        subst hc; exact hcard
      obtain ⟨r, hr⟩ := heven c
      exact ⟨r - 1, by omega⟩
    · have hxm : x ∉ S.filter (fun z => f z = c) := fun h => hc (mem_filter.mp h).2
      have hym : y ∉ (S.filter (fun z => f z = c)).erase x := fun h =>
        hc (hfy ▸ (mem_filter.mp (mem_of_mem_erase h)).2)
      rw [erase_eq_of_notMem hym, erase_eq_of_notMem hxm]
      exact heven c
  have hk1 : 1 ≤ k := by rw [← hS]; exact card_pos.mpr ⟨x, hx⟩
  obtain ⟨g', hg'inv, hg'S, hg'out⟩ := ih (k - 2) (by omega) _ hS'card heven'
  have hxS' : x ∉ (S.erase x).erase y := by simp
  have hyS' : y ∉ (S.erase x).erase y := by simp
  have hgx : g' x = x := hg'out x hxS'
  have hgy : g' y = y := hg'out y hyS'
  refine ⟨fun z => if z = x then y else if z = y then x else g' z, ?_, ?_, ?_⟩
  · intro z
    by_cases hzx : z = x
    · subst hzx; simp [hyx]
    by_cases hzy : z = y
    · subst hzy; simp [hyx]
    have h1 : g' z ≠ x := fun h => hzx (by rw [← hg'inv z, h, hgx])
    have h2 : g' z ≠ y := fun h => hzy (by rw [← hg'inv z, h, hgy])
    simp [hzx, hzy, h1, h2, hg'inv z]
  · intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [hyx, hfy]
    by_cases hzy : z = y
    · subst hzy; simp [hyx, hfy, Ne.symm hyx]
    have hz' : z ∈ (S.erase x).erase y := by simp [hz, hzx, hzy]
    simp only [hzx, hzy, if_false]
    exact hg'S z hz'
  · intro z hz
    have hzx : z ≠ x := fun h => hz (h ▸ hx)
    have hzy : z ≠ y := fun h => hz (h ▸ hyS)
    have hz' : z ∉ (S.erase x).erase y := by simp [hz]
    simp only [hzx, hzy, if_false]
    exact hg'out z hz'

theorem regroup {α M : Type*} [Fintype α] [LinearOrder α] [CommMonoid M] (σ : Equiv.Perm α)
    (hinv : Function.Involutive σ) (hfp : ∀ k, σ k ≠ k) (f : α → M) :
    ∏ x, f x = ∏ a ∈ univ.filter (fun a => a < σ a), (f a * f (σ a)) := by
  rw [← prod_filter_mul_prod_filter_not univ (fun a => a < σ a), prod_mul_distrib]
  congr 1
  apply Finset.prod_nbij' (fun a => σ a) (fun a => σ a)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, not_lt] at ha ⊢
    rw [hinv a]; exact lt_of_le_of_ne ha (hfp a)
  · intro a ha
    simp only [mem_filter, mem_univ, true_and, not_lt] at ha ⊢
    rw [hinv a]; exact le_of_lt ha
  · intro a _; exact hinv a
  · intro a _; exact hinv a
  · intro a _; rw [hinv a]

theorem card_F {α : Type*} [Fintype α] [LinearOrder α] (σ : Equiv.Perm α)
    (hinv : Function.Involutive σ) (hfp : ∀ k, σ k ≠ k) :
    2 * (univ.filter (fun a => a < σ a)).card = Fintype.card α := by
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => a < σ a)
  have h2 : (univ.filter (fun a => ¬ a < σ a)).card = (univ.filter (fun a => a < σ a)).card := by
    apply Finset.card_nbij' (fun a => σ a) (fun a => σ a)
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, not_lt, Set.mem_setOf_eq] at ha ⊢
      rw [hinv a]; exact lt_of_le_of_ne ha (hfp a)
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, not_lt, Set.mem_setOf_eq] at ha ⊢
      rw [hinv a]; exact le_of_lt ha
    · intro a _; exact hinv a
    · intro a _; exact hinv a
  rw [card_univ] at h1
  omega

def finTwoMulEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) where
  toFun p := ⟨2 * p.1.val + p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩
  invFun m := (⟨m.val / 2, by have := m.isLt; omega⟩, ⟨m.val % 2, by omega⟩)
  left_inv p := by
    have := p.2.isLt
    ext <;> simp <;> omega
  right_inv m := by
    ext; simp; omega

theorem prod_fin_two_mul {M : Type*} [CommMonoid M] (n : ℕ) (f : Fin (2 * n) → M) :
    ∏ m, f m = ∏ k : Fin n, (f ⟨2 * k.val, by omega⟩ * f ⟨2 * k.val + 1, by omega⟩) := by
  rw [← (finTwoMulEquiv n).prod_comp, Fintype.prod_prod_type]
  apply prod_congr rfl
  intro k _
  rw [Fin.prod_univ_two]
  rfl

theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] (n : ℕ) (f : Fin (2 * n) → M) :
    ∑ m, f m = ∑ k : Fin n, (f ⟨2 * k.val, by omega⟩ + f ⟨2 * k.val + 1, by omega⟩) := by
  rw [← (finTwoMulEquiv n).sum_comp, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro k _
  rw [Fin.sum_univ_two]
  rfl

theorem amgm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) (hs : s.Nonempty) :
    ∏ i ∈ s, x i ≤ ∑ i ∈ s, (1 / (s.card : ℝ)) * x i ^ s.card := by
  have hk : s.card ≠ 0 := hs.card_pos.ne'
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hk
  have := Real.geom_mean_le_arith_mean_weighted s (fun _ => 1 / (s.card : ℝ))
    (fun i => x i ^ s.card) (fun i _ => by positivity)
    (by rw [sum_const, nsmul_eq_mul]; field_simp) (fun i hi => pow_nonneg (hx i hi) _)
  calc ∏ i ∈ s, x i = ∏ i ∈ s, (x i ^ s.card) ^ (1 / (s.card : ℝ)) := by
        apply prod_congr rfl; intro i hi
        rw [one_div, Real.pow_rpow_inv_natCast (hx i hi) hk]
    _ ≤ _ := this


section Kern
variable {n1 n2 : ℕ}

def Kv (W : Fin n1 → Fin n2 → ℝ) : Fin n1 ⊕ Fin n2 → Fin n1 ⊕ Fin n2 → ℝ
  | Sum.inl i, Sum.inr j => W i j
  | Sum.inr j, Sum.inl i => W i j
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

def Zv (W : Fin n1 → Fin n2 → ℝ) (x : Fin n1 ⊕ Fin n2) : ℝ := ∑ y, Kv W x y

noncomputable def Tv (W : Fin n1 → Fin n2 → ℝ) (x y : Fin n1 ⊕ Fin n2) : ℝ :=
  Kv W x y / Zv W x

variable {W : Fin n1 → Fin n2 → ℝ}

lemma Kv_nonneg (hW : ∀ i j, 0 ≤ W i j) (x y : Fin n1 ⊕ Fin n2) : 0 ≤ Kv W x y := by
  cases x <;> cases y <;> simp [Kv, hW]

lemma Kv_symm (x y : Fin n1 ⊕ Fin n2) : Kv W x y = Kv W y x := by
  cases x <;> cases y <;> rfl

lemma Zv_inl (i : Fin n1) : Zv W (Sum.inl i) = ∑ j, W i j := by
  simp [Zv, Fintype.sum_sum_type, Kv]

lemma Zv_inr (j : Fin n2) : Zv W (Sum.inr j) = ∑ i, W i j := by
  simp [Zv, Fintype.sum_sum_type, Kv]

lemma Zv_nonneg (hW : ∀ i j, 0 ≤ W i j) (x : Fin n1 ⊕ Fin n2) : 0 ≤ Zv W x :=
  sum_nonneg fun y _ => Kv_nonneg hW x y

lemma Kv_le_Zv (hW : ∀ i j, 0 ≤ W i j) (x y : Fin n1 ⊕ Fin n2) : Kv W x y ≤ Zv W x :=
  single_le_sum (f := fun y => Kv W x y) (fun y _ => Kv_nonneg hW x y) (mem_univ y)

lemma Kv_eq (hW : ∀ i j, 0 ≤ W i j) (x y : Fin n1 ⊕ Fin n2) :
    Kv W x y = Zv W x * Tv W x y := by
  unfold Tv
  by_cases h : Zv W x = 0
  · have h1 := Kv_le_Zv hW x y
    have h2 := Kv_nonneg hW x y
    rw [h] at h1 ⊢
    simp only [div_zero, mul_zero]
    linarith
  · field_simp

lemma Tv_nonneg (hW : ∀ i j, 0 ≤ W i j) (x y : Fin n1 ⊕ Fin n2) : 0 ≤ Tv W x y :=
  div_nonneg (Kv_nonneg hW x y) (Zv_nonneg hW x)

lemma Tv_sum_le (x : Fin n1 ⊕ Fin n2) : ∑ y, Tv W x y ≤ 1 := by
  unfold Tv
  rw [← sum_div]
  exact div_self_le_one _

lemma Tv_inv (hW : ∀ i j, 0 ≤ W i j) (y : Fin n1 ⊕ Fin n2) :
    ∑ x, Zv W x * Tv W x y ≤ Zv W y := by
  calc ∑ x, Zv W x * Tv W x y = ∑ x, Kv W y x := by
        apply sum_congr rfl; intro x _; rw [← Kv_eq hW x y, Kv_symm]
    _ = Zv W y := rfl
    _ ≤ Zv W y := le_refl _

end Kern

section Walk
variable {n n1 n2 : ℕ}

def posE (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (m : Fin (2 * n)) : Fin n1 × Fin n2 :=
  if m.val % 2 = 0 then
    (rows ⟨m.val / 2, by have := m.isLt; omega⟩, cols ⟨m.val / 2, by have := m.isLt; omega⟩)
  else
    (rows (buchholzCyclicSucc (⟨m.val / 2, by have := m.isLt; omega⟩ : Fin n)),
      cols ⟨m.val / 2, by have := m.isLt; omega⟩)

def enc (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (t : Fin (2 * n)) : Fin n1 ⊕ Fin n2 :=
  if t.val % 2 = 0 then Sum.inl (rows ⟨t.val / 2, by have := t.isLt; omega⟩)
  else Sum.inr (cols ⟨t.val / 2, by have := t.isLt; omega⟩)

lemma posE_even (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (k : Fin n) :
    posE rows cols ⟨2 * k.val, by omega⟩ = (rows k, cols k) := by
  have h1 : (2 * k.val) % 2 = 0 := by omega
  have h2 : (2 * k.val) / 2 = k.val := by omega
  simp only [posE, h1, h2, if_true]

lemma posE_odd (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (k : Fin n) :
    posE rows cols ⟨2 * k.val + 1, by omega⟩ = (rows (buchholzCyclicSucc k), cols k) := by
  have h1 : ¬ (2 * k.val + 1) % 2 = 0 := by omega
  have h2 : (2 * k.val + 1) / 2 = k.val := by omega
  simp only [posE, h1, h2, if_false]

noncomputable def wfun {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (c : Fin n1 × Fin n2) : ℝ :=
  if c ∈ Omega then p⁻¹ * X c.1 c.2 else 0

lemma walkProduct_eq (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    buchholzWalkProduct Omega p X rows cols = ∏ m : Fin (2 * n), wfun Omega p X (posE rows cols m) := by
  rw [prod_fin_two_mul]
  unfold buchholzWalkProduct
  apply prod_congr rfl
  intro k _
  rw [posE_even, posE_odd]
  rfl

lemma matched_even (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (h : buchholzWalkMatched rows cols) (c : Fin n1 × Fin n2) :
    Even (univ.filter (fun m => posE rows cols m = c)).card := by
  have e : (univ.filter (fun m => posE rows cols m = c)).card = buchholzEdgeMultiplicity rows cols c := by
    rw [card_filter, sum_fin_two_mul]
    unfold buchholzEdgeMultiplicity
    rw [card_filter, card_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    rw [posE_even, posE_odd]
  rw [e]; exact h c

lemma S_at (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (m : Fin (2 * n)) :
    extF d (enc rows cols) m.val =
      if m.val % 2 = 0 then Sum.inl (posE rows cols m).1 else Sum.inr (posE rows cols m).2 := by
  unfold extF
  rw [dif_pos m.isLt]
  by_cases hm : m.val % 2 = 0
  · simp [enc, posE, hm]
  · simp [enc, posE, hm]

lemma S_succ (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (m : Fin (2 * n))
    (h : m.val + 1 < 2 * n) :
    extF d (enc rows cols) (m.val + 1) =
      if m.val % 2 = 0 then Sum.inr (posE rows cols m).2 else Sum.inl (posE rows cols m).1 := by
  unfold extF
  rw [dif_pos h]
  by_cases hm : m.val % 2 = 0
  · have h1 : ¬ (m.val + 1) % 2 = 0 := by omega
    have h2 : (m.val + 1) / 2 = m.val / 2 := by omega
    simp only [enc, posE, hm, h1, h2, if_true, if_false]
  · have h1 : (m.val + 1) % 2 = 0 := by omega
    simp only [enc, posE, hm, h1, if_true, if_false]
    congr 2
    apply Fin.ext
    simp only [buchholzCyclicSucc]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

lemma S_zero (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (hn : 1 ≤ n) :
    extF d (enc rows cols) 0 = Sum.inl (rows ⟨0, hn⟩) := by
  unfold extF
  rw [dif_pos (by omega)]
  simp [enc]

lemma Kv_S {W : Fin n1 → Fin n2 → ℝ} (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1)
    (cols : Fin n → Fin n2) (m : Fin (2 * n)) (h : m.val + 1 < 2 * n) :
    Kv W (extF d (enc rows cols) m.val) (extF d (enc rows cols) (m.val + 1)) =
      W (posE rows cols m).1 (posE rows cols m).2 := by
  rw [S_at, S_succ d rows cols m h]
  split_ifs <;> rfl

end Walk

section Chain
variable {n n1 n2 : ℕ}

def jpar (a m : ℕ) : ℕ := if a % 2 = m % 2 then a + 1 else a

def parF (σ : Equiv.Perm (Fin (2 * n))) (m : ℕ) : ℕ :=
  if h : m < 2 * n then
    (if (⟨m, h⟩ : Fin (2 * n)) < σ ⟨m, h⟩ then m else jpar (σ ⟨m, h⟩).val m)
  else 0

noncomputable def KtF (σ : Equiv.Perm (Fin (2 * n))) (W : Fin n1 → Fin n2 → ℝ) (m : ℕ)
    (x y : Fin n1 ⊕ Fin n2) : ℝ :=
  if h : m < 2 * n then
    (if (⟨m, h⟩ : Fin (2 * n)) < σ ⟨m, h⟩ then Tv W x y else if y = x then 1 else 0)
  else if y = x then 1 else 0

lemma parF_le (σ : Equiv.Perm (Fin (2 * n))) (hfp : ∀ k, σ k ≠ k) (m : ℕ) : parF σ m ≤ m := by
  unfold parF
  split_ifs with h1 h2
  · exact le_refl _
  · have hlt : (σ ⟨m, h1⟩).val < m :=
      Fin.lt_def.mp (lt_of_le_of_ne (not_lt.mp h2) (hfp ⟨m, h1⟩))
    unfold jpar; split_ifs <;> omega
  · exact Nat.zero_le _

lemma KtF_cases (σ : Equiv.Perm (Fin (2 * n))) (W : Fin n1 → Fin n2 → ℝ) (m : ℕ) :
    KtF σ W m = Tv W ∨ KtF σ W m = (fun x y => if y = x then (1:ℝ) else 0) := by
  by_cases h : m < 2 * n
  · by_cases h2 : (⟨m, h⟩ : Fin (2 * n)) < σ ⟨m, h⟩
    · left; funext x y; simp [KtF, h, h2]
    · right; funext x y; simp [KtF, h, h2]
  · right; funext x y; simp [KtF, h]

lemma KtF_nonneg (σ : Equiv.Perm (Fin (2 * n))) {W : Fin n1 → Fin n2 → ℝ}
    (hW : ∀ i j, 0 ≤ W i j) (m : ℕ) (x y : Fin n1 ⊕ Fin n2) : 0 ≤ KtF σ W m x y := by
  rcases KtF_cases σ W m with h | h <;> rw [h]
  · exact Tv_nonneg hW x y
  · simp only; split_ifs <;> norm_num

lemma KtF_sub (σ : Equiv.Perm (Fin (2 * n))) (W : Fin n1 → Fin n2 → ℝ) (m : ℕ)
    (x : Fin n1 ⊕ Fin n2) : ∑ y, KtF σ W m x y ≤ 1 := by
  rcases KtF_cases σ W m with h | h <;> rw [h]
  · exact Tv_sum_le x
  · simp

lemma KtF_inv (σ : Equiv.Perm (Fin (2 * n))) {W : Fin n1 → Fin n2 → ℝ}
    (hW : ∀ i j, 0 ≤ W i j) (m : ℕ) (y : Fin n1 ⊕ Fin n2) :
    ∑ x, Zv W x * KtF σ W m x y ≤ Zv W y := by
  rcases KtF_cases σ W m with h | h <;> rw [h]
  · exact Tv_inv hW y
  · simp

lemma S_pair (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (σ : Equiv.Perm (Fin (2 * n))) (hfp : ∀ k, σ k ≠ k)
    (hc : ∀ k, posE rows cols (σ k) = posE rows cols k) (M : Fin (2 * n))
    (hM : ¬ M < σ M) (h : M.val + 1 < 2 * n) :
    extF d (enc rows cols) (M.val + 1) = extF d (enc rows cols) (jpar (σ M).val M.val) := by
  have hlt : (σ M).val < M.val := Fin.lt_def.mp (lt_of_le_of_ne (not_lt.mp hM) (hfp M))
  have hE := hc M
  by_cases hp : (σ M).val % 2 = M.val % 2
  · have hj : jpar (σ M).val M.val = (σ M).val + 1 := by simp [jpar, hp]
    rw [hj, S_succ d rows cols M h, S_succ d rows cols (σ M) (by omega), hE, hp]
  · have hj : jpar (σ M).val M.val = (σ M).val := by simp [jpar, hp]
    rw [hj, S_succ d rows cols M h, S_at d rows cols (σ M), hE]
    by_cases hm : M.val % 2 = 0
    · rw [if_pos hm, if_neg (by omega)]
    · rw [if_neg hm, if_pos (by omega)]

lemma prod_range_pred {M : Type*} [CommMonoid M] (f : ℕ → M) (N : ℕ) (hN : 1 ≤ N) :
    ∏ m ∈ range N, f m = (∏ m ∈ range (N - 1), f m) * f (N - 1) := by
  have := prod_range_succ f (N - 1)
  rw [Nat.sub_add_cancel hN] at this
  exact this

lemma chain_eq (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (σ : Equiv.Perm (Fin (2 * n))) (hfp : ∀ k, σ k ≠ k)
    (hc : ∀ k, posE rows cols (σ k) = posE rows cols k) (W : Fin n1 → Fin n2 → ℝ) (hn : 1 ≤ n) :
    ∏ m ∈ range (2 * n - 1), KtF σ W m (extF d (enc rows cols) (parF σ m))
        (extF d (enc rows cols) (m + 1)) =
      ∏ a ∈ univ.filter (fun a => a < σ a),
        Tv W (extF d (enc rows cols) a.val) (extF d (enc rows cols) (a.val + 1)) := by
  set S := extF d (enc rows cols) with hS
  let φ : ℕ → ℝ := fun m => if h : m < 2 * n then
      (if (⟨m, h⟩ : Fin (2 * n)) < σ ⟨m, h⟩ then Tv W (S m) (S (m + 1)) else 1) else 1
  rw [prod_filter]
  have e1 : ∏ a : Fin (2 * n), (if a < σ a then Tv W (S a.val) (S (a.val + 1)) else 1)
      = ∏ a : Fin (2 * n), φ a.val := by
    apply prod_congr rfl; intro a _
    simp only [φ, dif_pos a.isLt, Fin.eta]
  rw [e1, Fin.prod_univ_eq_prod_range φ (2 * n), prod_range_pred φ (2 * n) (by omega)]
  have hlast : φ (2 * n - 1) = 1 := by
    simp only [φ, dif_pos (show 2 * n - 1 < 2 * n by omega)]
    rw [if_neg]
    intro hlt
    have h1 := Fin.lt_def.mp hlt
    have h2 := (σ ⟨2 * n - 1, by omega⟩).isLt
    simp only at h1
    omega
  rw [hlast, mul_one]
  apply prod_congr rfl
  intro m hm
  have hm' : m + 1 < 2 * n := by have := mem_range.mp hm; omega
  have hm2 : m < 2 * n := by omega
  simp only [φ, KtF, parF, dif_pos hm2]
  by_cases h2 : (⟨m, hm2⟩ : Fin (2 * n)) < σ ⟨m, hm2⟩
  · simp only [h2, if_true]
  · simp only [h2, if_false]
    rw [if_pos]
    exact S_pair d rows cols σ hfp hc ⟨m, hm2⟩ h2 hm'

noncomputable def Wf {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) : ℝ := wfun Omega p X (i, j) ^ 2

lemma product_eq (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (d : Fin n1 ⊕ Fin n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (σ : Equiv.Perm (Fin (2 * n))) (hinv : Function.Involutive σ) (hfp : ∀ k, σ k ≠ k)
    (hc : ∀ k, posE rows cols (σ k) = posE rows cols k) :
    buchholzWalkProduct Omega p X rows cols =
      (∏ a ∈ univ.filter (fun a => a < σ a), Zv (Wf Omega p X) (extF d (enc rows cols) a.val)) *
      ∏ a ∈ univ.filter (fun a => a < σ a),
        Tv (Wf Omega p X) (extF d (enc rows cols) a.val) (extF d (enc rows cols) (a.val + 1)) := by
  have hW : ∀ i j, 0 ≤ Wf Omega p X i j := fun i j => sq_nonneg _
  rw [walkProduct_eq, regroup σ hinv hfp, ← prod_mul_distrib]
  apply prod_congr rfl
  intro a ha
  have ha' : a.val + 1 < 2 * n := by
    have h1 := Fin.lt_def.mp (mem_filter.mp ha).2
    have h2 := (σ a).isLt
    omega
  rw [hc a, ← Kv_eq hW, Kv_S d rows cols a ha']
  simp only [Wf, Prod.mk.eta, sq]

lemma product_nonneg (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2)
    (σ : Equiv.Perm (Fin (2 * n))) (hinv : Function.Involutive σ) (hfp : ∀ k, σ k ≠ k)
    (hc : ∀ k, posE rows cols (σ k) = posE rows cols k) :
    0 ≤ buchholzWalkProduct Omega p X rows cols := by
  rw [walkProduct_eq, regroup σ hinv hfp]
  apply prod_nonneg
  intro a _
  rw [hc a]
  exact mul_self_nonneg _

end Chain

section Final
variable {n n1 n2 : ℕ}

lemma chain_bound' {V : Type*} [Fintype V] (d : V) (Z ρ : V → ℝ) (par : ℕ → ℕ)
    (Kt : ℕ → V → V → ℝ) (hpar : ∀ m, par m ≤ m)
    (hK0 : ∀ m x y, 0 ≤ Kt m x y) (hKsub : ∀ m x, ∑ y, Kt m x y ≤ 1)
    (hKinv : ∀ m y, ∑ x, Z x * Kt m x y ≤ Z y)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : ∀ x, ρ x ≤ Z x) (M : ℕ) (hM : 1 ≤ M)
    (g : V → ℝ) (hg : ∀ x, 0 ≤ g x) (tstar : ℕ) (ht : tstar < M) :
    ∑ s : Fin M → V, ρ (extF d s 0) *
        (∏ m ∈ range (M - 1), Kt m (extF d s (par m)) (extF d s (m+1))) * g (extF d s tstar)
      ≤ ∑ x, Z x * g x := by
  obtain ⟨N, rfl⟩ : ∃ N, M = N + 1 := ⟨M - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact chain_bound d Z ρ par Kt hpar hK0 hKsub hKinv hρ0 hρ N g hg tstar (by omega)

lemma enc_injective :
    Function.Injective (fun q : (Fin n → Fin n1) × (Fin n → Fin n2) => enc q.1 q.2) := by
  intro q1 q2 h
  have h' := congrFun h
  apply Prod.ext
  · funext k
    have := h' ⟨2 * k.val, by omega⟩
    have e1 : (2 * k.val) % 2 = 0 := by omega
    have e2 : (2 * k.val) / 2 = k.val := by omega
    simp only [enc, e1, e2, if_true, Sum.inl.injEq] at this
    exact this
  · funext k
    have := h' ⟨2 * k.val + 1, by omega⟩
    have e1 : ¬ (2 * k.val + 1) % 2 = 0 := by omega
    have e2 : (2 * k.val + 1) / 2 = k.val := by omega
    simp only [enc, e1, e2, if_false, Sum.inr.injEq] at this
    exact this

lemma sum_walk_le (G : (Fin (2 * n) → Fin n1 ⊕ Fin n2) → ℝ) (hG : ∀ s, 0 ≤ G s) :
    ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2, G (enc rows cols) ≤ ∑ s, G s := by
  rw [← Fintype.sum_prod_type' (f := fun rows cols => G (enc rows cols))]
  have := Finset.sum_map (univ : Finset ((Fin n → Fin n1) × (Fin n → Fin n2)))
    ⟨_, enc_injective⟩ G
  simp only [Function.Embedding.coeFn_mk] at this
  rw [← this]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun s _ _ => hG s)

theorem per_pairing (hn : 1 ≤ n) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (σ : Equiv.Perm (Fin (2 * n))) (hinv : Function.Involutive σ) (hfp : ∀ k, σ k ≠ k) :
    ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
      (if (∀ k, posE rows cols (σ k) = posE rows cols k) then
        buchholzWalkProduct Omega p X rows cols else 0)
      ≤ max (∑ i, Zv (Wf Omega p X) (Sum.inl i) ^ n) (∑ j, Zv (Wf Omega p X) (Sum.inr j) ^ n) := by
  set W := Wf Omega p X with hWdef
  have hW : ∀ i j, 0 ≤ W i j := fun i j => sq_nonneg _
  have hA0 : 0 ≤ ∑ i, Zv W (Sum.inl i) ^ n := sum_nonneg fun i _ => pow_nonneg (Zv_nonneg hW _) _
  rcases Nat.eq_zero_or_pos n1 with h0 | h0
  · subst h0
    have : IsEmpty (Fin n → Fin 0) := ⟨fun f => (f ⟨0, hn⟩).elim0⟩
    rw [Finset.univ_eq_empty, sum_empty]
    exact le_max_of_le_left hA0
  set d : Fin n1 ⊕ Fin n2 := Sum.inl ⟨0, h0⟩ with hd
  set F := univ.filter (fun a : Fin (2 * n) => a < σ a) with hF
  have h0F : (⟨0, by omega⟩ : Fin (2 * n)) ∈ F := by
    rw [hF, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h1 := hfp ⟨0, by omega⟩
    have h2 : (σ ⟨0, by omega⟩).val ≠ 0 := fun h => h1 (Fin.ext h)
    rw [Fin.lt_def]
    simp only
    omega
  have hFcard : F.card = n := by
    have := card_F σ hinv hfp
    rw [Fintype.card_fin, ← hF] at this
    omega
  let ρ : Fin n1 ⊕ Fin n2 → ℝ := fun x => Sum.elim (fun i => Zv W (Sum.inl i)) (fun _ => 0) x
  have hρ0 : ∀ x, 0 ≤ ρ x := by intro x; cases x <;> simp [ρ, Zv_nonneg hW]
  have hρ : ∀ x, ρ x ≤ Zv W x := by intro x; cases x <;> simp [ρ, Zv_nonneg hW]
  let chain : (Fin (2 * n) → Fin n1 ⊕ Fin n2) → ℝ := fun s =>
    ∏ m ∈ range (2 * n - 1), KtF σ W m (extF d s (parF σ m)) (extF d s (m + 1))
  have hchain0 : ∀ s, 0 ≤ chain s := fun s => prod_nonneg fun m _ => KtF_nonneg σ hW _ _ _
  have hWC : ∀ (g : Fin n1 ⊕ Fin n2 → ℝ), (∀ x, 0 ≤ g x) → ∀ t < 2 * n,
      ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
        ρ (extF d (enc rows cols) 0) * chain (enc rows cols) * g (extF d (enc rows cols) t)
        ≤ ∑ x, Zv W x * g x := by
    intro g hg t ht
    refine le_trans (sum_walk_le (fun s => ρ (extF d s 0) * chain s * g (extF d s t))
      (fun s => mul_nonneg (mul_nonneg (hρ0 _) (hchain0 s)) (hg _))) ?_
    exact chain_bound' d (Zv W) ρ (parF σ) (KtF σ W) (parF_le σ hfp) (KtF_nonneg σ hW)
      (KtF_sub σ W) (KtF_inv σ hW) hρ0 hρ (2 * n) (by omega) g hg t ht
  let hL : Fin n1 ⊕ Fin n2 → ℝ := fun x =>
    Sum.elim (fun i => Zv W (Sum.inl i) ^ (n - 1)) (fun _ => 0) x
  let hR : Fin n1 ⊕ Fin n2 → ℝ := fun x =>
    Sum.elim (fun _ => 0) (fun j => Zv W (Sum.inr j) ^ (n - 1)) x
  have hL0 : ∀ x, 0 ≤ hL x := by
    intro x; cases x <;> simp [hL, pow_nonneg (Zv_nonneg hW _)]
  have hR0 : ∀ x, 0 ≤ hR x := by
    intro x; cases x <;> simp [hR, pow_nonneg (Zv_nonneg hW _)]
  have hLsum : ∑ x, Zv W x * hL x = ∑ i, Zv W (Sum.inl i) ^ n := by
    rw [Fintype.sum_sum_type]
    simp only [hL, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, add_zero]
    apply sum_congr rfl; intro i _
    rw [← pow_succ']; congr 1; omega
  have hRsum : ∑ x, Zv W x * hR x = ∑ j, Zv W (Sum.inr j) ^ n := by
    rw [Fintype.sum_sum_type]
    simp only [hR, Sum.elim_inl, Sum.elim_inr, mul_zero, sum_const_zero, zero_add]
    apply sum_congr rfl; intro i _
    rw [← pow_succ']; congr 1; omega
  have hpt : ∀ (rows : Fin n → Fin n1) (cols : Fin n → Fin n2), (∀ k, posE rows cols (σ k) = posE rows cols k) →
      buchholzWalkProduct Omega p X rows cols = ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
        ∏ a ∈ F.erase ⟨0, by omega⟩, Zv W (extF d (enc rows cols) a.val) := by
    intro rows cols hc
    rw [product_eq Omega p X d rows cols σ hinv hfp hc, ← chain_eq d rows cols σ hfp hc W hn,
      ← mul_prod_erase F _ h0F]
    have : ρ (extF d (enc rows cols) 0) =
        Zv W (extF d (enc rows cols) (⟨0, by omega⟩ : Fin (2 * n)).val) := by
      simp only [ρ]
      rw [S_zero d rows cols hn]
      rfl
    rw [this]
    ring
  have hga : ∀ (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (a : Fin (2 * n)), Zv W (extF d (enc rows cols) a.val) ^ (n - 1) =
      (if a.val % 2 = 0 then hL else hR) (extF d (enc rows cols) a.val) := by
    intro rows cols a
    rw [S_at d rows cols a]
    by_cases ha : a.val % 2 = 0 <;> simp [ha, hL, hR]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    have hFe : F.erase ⟨0, by omega⟩ = ∅ := by
      rw [← card_eq_zero, card_erase_of_mem h0F, hFcard]; omega
    calc _ ≤ ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
          ρ (extF d (enc rows cols) 0) * chain (enc rows cols) * hL (extF d (enc rows cols) 0) := by
          apply sum_le_sum; intro rows _; apply sum_le_sum; intro cols _
          split_ifs with hc
          · rw [hpt rows cols hc, hFe, prod_empty, S_zero d rows cols hn]
            simp [hL, hn1]
          · exact mul_nonneg (mul_nonneg (hρ0 _) (hchain0 _)) (hL0 _)
      _ ≤ ∑ x, Zv W x * hL x := hWC hL hL0 0 (by omega)
      _ = _ := hLsum
      _ ≤ _ := le_max_left _ _
  · set F' := F.erase ⟨0, by omega⟩ with hF'
    have hF'card : F'.card = n - 1 := by rw [hF', card_erase_of_mem h0F, hFcard]
    have hF'ne : F'.Nonempty := by rw [← card_pos, hF'card]; omega
    let c : ℝ := 1 / ((n - 1 : ℕ) : ℝ)
    have hc0 : 0 ≤ c := by positivity
    let ga : Fin (2 * n) → Fin n1 ⊕ Fin n2 → ℝ := fun a => if a.val % 2 = 0 then hL else hR
    have hga0 : ∀ a x, 0 ≤ ga a x := by
      intro a x; simp only [ga]; split_ifs
      · exact hL0 x
      · exact hR0 x
    have step1 : ∀ (rows : Fin n → Fin n1) (cols : Fin n → Fin n2),
        (if (∀ k, posE rows cols (σ k) = posE rows cols k) then
          buchholzWalkProduct Omega p X rows cols else 0) ≤
        ∑ a ∈ F', c * (ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
          ga a (extF d (enc rows cols) a.val)) := by
      intro rows cols
      split_ifs with hc
      · rw [hpt rows cols hc]
        have am := amgm F' (fun a => Zv W (extF d (enc rows cols) a.val))
          (fun a _ => Zv_nonneg hW _) hF'ne
        rw [hF'card] at am
        calc ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
              ∏ a ∈ F', Zv W (extF d (enc rows cols) a.val)
            ≤ ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
              ∑ a ∈ F', c * Zv W (extF d (enc rows cols) a.val) ^ (n - 1) :=
              mul_le_mul_of_nonneg_left am (mul_nonneg (hρ0 _) (hchain0 _))
          _ = _ := by
              rw [mul_sum]; apply sum_congr rfl; intro a _
              rw [hga rows cols a]
              ring
      · exact sum_nonneg fun a _ =>
          mul_nonneg hc0 (mul_nonneg (mul_nonneg (hρ0 _) (hchain0 _)) (hga0 _ _))
    calc _ ≤ ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2, ∑ a ∈ F',
          c * (ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
            ga a (extF d (enc rows cols) a.val)) := by
          apply sum_le_sum; intro rows _; apply sum_le_sum; intro cols _; exact step1 rows cols
      _ = ∑ rows : Fin n → Fin n1, ∑ a ∈ F', ∑ cols : Fin n → Fin n2,
          c * (ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
            ga a (extF d (enc rows cols) a.val)) :=
          sum_congr rfl (fun rows _ => Finset.sum_comm)
      _ = ∑ a ∈ F', ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
          c * (ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
            ga a (extF d (enc rows cols) a.val)) := Finset.sum_comm
      _ = ∑ a ∈ F', c * ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
          ρ (extF d (enc rows cols) 0) * chain (enc rows cols) *
            ga a (extF d (enc rows cols) a.val) := by
          apply sum_congr rfl; intro a _
          rw [mul_sum]; apply sum_congr rfl; intro rows _; rw [mul_sum]
      _ ≤ ∑ a ∈ F', c * max (∑ i, Zv W (Sum.inl i) ^ n) (∑ j, Zv W (Sum.inr j) ^ n) := by
          apply sum_le_sum; intro a _
          apply mul_le_mul_of_nonneg_left _ hc0
          refine le_trans (hWC (ga a) (hga0 a) a.val a.isLt) ?_
          simp only [ga]
          split_ifs
          · rw [hLsum]; exact le_max_left _ _
          · rw [hRsum]; exact le_max_right _ _
      _ = _ := by
          rw [sum_const, hF'card, nsmul_eq_mul]
          have : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
            have : 1 ≤ n - 1 := by omega
            exact_mod_cast (show n - 1 ≠ 0 by omega)
          simp only [c]
          field_simp

end Final

lemma Zv_inl_eq {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (i : Fin n1) :
    Zv (Wf Omega p X) (Sum.inl i) =
      p⁻¹ ^ 2 * (Finset.univ.sum (fun j : Fin n2 => if (i, j) ∈ Omega then X i j ^ 2 else 0)) := by
  rw [Zv_inl, mul_sum]
  apply sum_congr rfl; intro j _
  simp only [Wf, wfun]
  split_ifs <;> ring

lemma Zv_inr_eq {n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (j : Fin n2) :
    Zv (Wf Omega p X) (Sum.inr j) =
      p⁻¹ ^ 2 * (Finset.univ.sum (fun i : Fin n1 => if (i, j) ∈ Omega then X i j ^ 2 else 0)) := by
  rw [Zv_inr, mul_sum]
  apply sum_congr rfl; intro i _
  simp only [Wf, wfun]
  split_ifs <;> ring

lemma rhs_nonneg {n n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    0 ≤ ∑ σ : BuchholzPairing n, (if (∀ k, posE rows cols (σ.1 k) = posE rows cols k) then
        buchholzWalkProduct Omega p X rows cols else 0) := by
  apply sum_nonneg
  intro σ _
  split_ifs with hc
  · exact product_nonneg Omega p X rows cols σ.1 σ.2.1 σ.2.2 hc
  · exact le_refl 0

lemma matched_le {n n1 n2 : ℕ} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) (hm : buchholzWalkMatched rows cols) :
    buchholzWalkProduct Omega p X rows cols ≤
      ∑ σ : BuchholzPairing n, (if (∀ k, posE rows cols (σ.1 k) = posE rows cols k) then
        buchholzWalkProduct Omega p X rows cols else 0) := by
  have hnn : ∀ σ : BuchholzPairing n, 0 ≤ (if (∀ k, posE rows cols (σ.1 k) = posE rows cols k) then
      buchholzWalkProduct Omega p X rows cols else 0) := by
    intro σ
    split_ifs with hc
    · exact product_nonneg Omega p X rows cols σ.1 σ.2.1 σ.2.2 hc
    · exact le_refl 0
  obtain ⟨g, hg, hgS, -⟩ := exists_pairing (posE rows cols) univ
    (fun c => matched_even rows cols hm c)
  let σ0 : BuchholzPairing n := ⟨hg.toPerm g,
    by rw [Function.Involutive.coe_toPerm]; exact hg,
    fun k => by rw [Function.Involutive.coe_toPerm]; exact (hgS k (mem_univ k)).1⟩
  have hc0 : ∀ k, posE rows cols (σ0.1 k) = posE rows cols k := by
    intro k
    show posE rows cols ((hg.toPerm g) k) = _
    rw [Function.Involutive.coe_toPerm]
    exact (hgS k (mem_univ k)).2
  have := single_le_sum (f := fun σ : BuchholzPairing n =>
    (if (∀ k, posE rows cols (σ.1 k) = posE rows cols k) then
      buchholzWalkProduct Omega p X rows cols else 0)) (fun σ _ => hnn σ) (mem_univ σ0)
  simp only [if_pos hc0] at this
  exact this

end SolE8b03350

set_option maxHeartbeats 4000000 in
open MatrixCompletion in
theorem SolE8b03350.pairing_sum_bound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ∑ _pairing : BuchholzPairing n,
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  unfold buchholzMatchedWalkSum
  simp only [← SolE8b03350.Zv_inl_eq, ← SolE8b03350.Zv_inr_eq]
  calc _
      ≤ ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2, ∑ σ : BuchholzPairing n,
          (if (∀ k, SolE8b03350.posE rows cols (σ.1 k) = SolE8b03350.posE rows cols k) then
            buchholzWalkProduct Omega p X rows cols else 0) :=
        Finset.sum_le_sum fun rows _ => Finset.sum_le_sum fun cols _ => by
          split_ifs with hm
          · exact SolE8b03350.matched_le Omega p X rows cols hm
          · exact SolE8b03350.rhs_nonneg Omega p X rows cols
    _ = ∑ rows : Fin n → Fin n1, ∑ σ : BuchholzPairing n, ∑ cols : Fin n → Fin n2,
          (if (∀ k, SolE8b03350.posE rows cols (σ.1 k) = SolE8b03350.posE rows cols k) then
            buchholzWalkProduct Omega p X rows cols else 0) :=
        Finset.sum_congr rfl (fun rows _ => Finset.sum_comm)
    _ = ∑ σ : BuchholzPairing n, ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
          (if (∀ k, SolE8b03350.posE rows cols (σ.1 k) = SolE8b03350.posE rows cols k) then
            buchholzWalkProduct Omega p X rows cols else 0) := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum fun σ _ =>
        SolE8b03350.per_pairing hn Omega p X σ.1 σ.2.1 σ.2.2

namespace SolE8b03350


lemma cycleType_of_pairing {n : ℕ} (hn : 1 ≤ n) (σ : BuchholzPairing n) :
    (σ.1).cycleType = Multiset.replicate n 2 := by
  obtain ⟨g, hinv, hfp⟩ := σ
  have hsupp : g.support = Finset.univ := by
    ext k
    simp [Equiv.Perm.mem_support, hfp k]
  have hsq : g ^ 2 = 1 := by
    ext k
    simp [sq, Equiv.Perm.mul_apply, hinv k]
  have hne : g ≠ 1 := by
    intro h
    have h0 := hfp ⟨0, by omega⟩
    rw [h] at h0
    exact h0 rfl
  have hord : orderOf g = 2 := orderOf_eq_prime hsq hne
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hm
  have hsum := Equiv.Perm.sum_cycleType g
  rw [hm, hsupp, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hmn : m + 1 = n := by omega
  show g.cycleType = _
  rw [hm, hmn]

lemma card_pairing_mul {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (BuchholzPairing n) * (2 ^ n * n.factorial) ≤ (2 * n).factorial := by
  classical
  have hinj : Fintype.card (BuchholzPairing n) ≤
      (Finset.univ.filter (fun g : Equiv.Perm (Fin (2 * n)) =>
        g.cycleType = Multiset.replicate n 2)).card := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
    · intro σ _
      simp [cycleType_of_pairing hn σ]
    · intro a _ b _ h
      exact Subtype.ext h
  have key := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (2 * n)) (Multiset.replicate n 2)
  have hne : n ≠ 0 := by omega
  have htf : (Multiset.replicate n 2).toFinset = {2} := by
    ext a
    simp [hne]
  rw [htf] at key
  simp only [Fintype.card_fin, Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate,
    Finset.prod_singleton, Multiset.count_replicate_self] at key
  rw [if_pos ⟨by omega, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩] at key
  have h0 : 2 * n - n * 2 = 0 := by omega
  rw [h0, Nat.factorial_zero, one_mul] at key
  calc Fintype.card (BuchholzPairing n) * (2 ^ n * n.factorial)
      ≤ _ * (2 ^ n * n.factorial) := Nat.mul_le_mul_right _ hinj
    _ = _ := key


end SolE8b03350

set_option maxHeartbeats 4000000 in
open MatrixCompletion in
theorem SolE8b03350.energy_bound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
  have h1 := SolE8b03350.pairing_sum_bound n hn Omega p hp X
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  refine h1.trans ?_
  have hM : 0 ≤ max
            (∑ i : Fin n1,
              (p⁻¹ ^ 2 *
                (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n)
            (∑ j : Fin n2,
              (p⁻¹ ^ 2 *
                (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n) := by
    refine le_max_of_le_left (Finset.sum_nonneg fun i _ => pow_nonneg
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => ?_)) n)
    split_ifs
    · exact sq_nonneg _
    · exact le_refl 0
  apply mul_le_mul_of_nonneg_right _ hM
  rw [le_div_iff₀ (by positivity)]
  have hc := SolE8b03350.card_pairing_mul hn
  exact_mod_cast hc


namespace SolE8b03350

lemma gram_row_eq {n n1 n2 : ℕ} (hn : 1 ≤ n) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) :
    (sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n) =
      ∑ i : Fin n1,
        (p⁻¹ ^ 2 * (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  unfold sampledRowGramSchatten
  simp only [Real.rpow_eq_pow]
  have hcast : (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hterm : ∀ i : Fin n1,
      (p⁻¹ * Real.sqrt (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^
          ((2 * n : ℕ) : ℝ) =
        (p⁻¹ ^ 2 * (∑ j : Fin n2, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
    intro i
    have hE : 0 ≤ ∑ j : Fin n2, (if (i, j) ∈ Omega then X i j ^ 2 else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
    rw [Real.rpow_natCast, pow_mul, mul_pow, Real.sq_sqrt hE]
  simp_rw [hterm]
  refine Real.rpow_inv_natCast_pow ?_ (by omega)
  refine Finset.sum_nonneg fun i _ => pow_nonneg (mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun j _ => ?_)) n
  split_ifs <;> positivity

lemma gram_col_eq {n n1 n2 : ℕ} (hn : 1 ≤ n) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) :
    (sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n) =
      ∑ j : Fin n2,
        (p⁻¹ ^ 2 * (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
  unfold sampledColumnGramSchatten
  simp only [Real.rpow_eq_pow]
  have hcast : (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hterm : ∀ j : Fin n2,
      (p⁻¹ * Real.sqrt (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^
          ((2 * n : ℕ) : ℝ) =
        (p⁻¹ ^ 2 * (∑ i : Fin n1, if (i, j) ∈ Omega then X i j ^ 2 else 0)) ^ n := by
    intro j
    have hE : 0 ≤ ∑ i : Fin n1, (if (i, j) ∈ Omega then X i j ^ 2 else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
    rw [Real.rpow_natCast, pow_mul, mul_pow, Real.sq_sqrt hE]
  simp_rw [hterm]
  refine Real.rpow_inv_natCast_pow ?_ (by omega)
  refine Finset.sum_nonneg fun j _ => pow_nonneg (mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg fun i _ => ?_)) n
  split_ifs <;> positivity

end SolE8b03350

open MatrixCompletion in
theorem SolE8b03350.matched_bound
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    buchholzMatchedWalkSum n Omega p X
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  rw [SolE8b03350.gram_row_eq hn Omega p X, SolE8b03350.gram_col_eq hn Omega p X]
  exact SolE8b03350.energy_bound n hn Omega p hp X

namespace Sol40809130

lemma pow_succ_apply_walk {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    ∀ (m : ℕ) (a c : ι), (M ^ (m + 1)) a c =
      ∑ v : Fin (m + 1) → ι, (if v 0 = a then (1 : ℝ) else 0) *
        (∏ k : Fin m, M (v k.castSucc) (v k.succ)) * M (v (Fin.last m)) c := by
  intro m
  induction m with
  | zero =>
    intro a c
    rw [pow_one, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp [Equiv.funUnique_symm_apply]
  | succ m ih =>
    intro a c
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    rw [← (Fin.snocEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
    simp only [show ∀ q : ι × (Fin (m + 1) → ι), (Fin.snocEquiv (fun _ => ι)) q = Fin.snoc q.2 q.1
      from fun q => rfl]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have h0 : (Fin.snoc v b : Fin (m + 2) → ι) 0 = v 0 :=
      Fin.snoc_castSucc (α := fun _ => ι) b v 0
    rw [Fin.prod_univ_castSucc, h0]
    simp only [Fin.snoc_castSucc, Fin.succ_castSucc, Fin.succ_last, Fin.snoc_last]
    ring

lemma trace_pow_walk {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (m : ℕ) :
    Matrix.trace (M ^ (m + 1)) =
      ∑ v : Fin (m + 1) → ι, ∏ k : Fin (m + 1), M (v k) (v (buchholzCyclicSucc k)) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  simp_rw [pow_succ_apply_walk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hc1 : ∀ k : Fin m, buchholzCyclicSucc (k.castSucc) = k.succ := by
    intro k
    ext
    simp only [buchholzCyclicSucc, Fin.val_castSucc, Fin.val_succ]
    exact Nat.mod_eq_of_lt (by omega)
  have hc2 : buchholzCyclicSucc (Fin.last m) = 0 := by
    ext
    simp [buchholzCyclicSucc]
  rw [Fin.prod_univ_castSucc]
  simp only [hc1, hc2]

lemma trace_eq_walk (n : ℕ) (hn : 1 ≤ n) {n1 n2 : ℕ} (S : RealMatrix n1 n2) :
    Matrix.trace ((S * S.transpose) ^ n) =
      ∑ rows : Fin n → Fin n1, ∑ cols : Fin n → Fin n2,
        ∏ k : Fin n, S (rows k) (cols k) * S (rows (buchholzCyclicSucc k)) (cols k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [trace_pow_walk]
  refine Finset.sum_congr rfl (fun rows _ => ?_)
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Fintype.prod_sum]

lemma entry_split {n1 n2 : ℕ} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    rademacherSampledMatrix Omega eps p X i j =
      (if (i, j) ∈ Omega then p⁻¹ * X i j else 0) * rademacherSign eps i j := by
  unfold rademacherSampledMatrix
  split_ifs <;> ring

lemma walk_split {n n1 n2 : ℕ} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    (∏ k : Fin n, rademacherSampledMatrix Omega eps p X (rows k) (cols k) *
        rademacherSampledMatrix Omega eps p X (rows (buchholzCyclicSucc k)) (cols k)) =
      buchholzWalkProduct Omega p X rows cols *
        ∏ k : Fin n, (rademacherSign eps (rows k) (cols k) *
          rademacherSign eps (rows (buchholzCyclicSucc k)) (cols k)) := by
  simp only [entry_split]
  unfold buchholzWalkProduct
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  ring

lemma sign_prod_eq {n n1 n2 : ℕ} (eps : Finset (Fin n1 × Fin n2))
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    (∏ k : Fin n, (rademacherSign eps (rows k) (cols k) *
          rademacherSign eps (rows (buchholzCyclicSucc k)) (cols k))) =
      ∏ x : Fin n1 × Fin n2, (if x ∈ eps then (1 : ℝ) else -1) ^
        buchholzEdgeMultiplicity rows cols x := by
  have key : ∀ g : Fin n → Fin n1 × Fin n2,
      ∏ k, (if g k ∈ eps then (1 : ℝ) else -1) =
        ∏ x, (if x ∈ eps then (1 : ℝ) else -1) ^ (univ.filter (fun k => g k = x)).card := by
    intro g
    rw [← Finset.prod_fiberwise' univ g (fun x => if x ∈ eps then (1 : ℝ) else -1)]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [Finset.prod_const]
  rw [Finset.prod_mul_distrib]
  have e1 := key (fun k => (rows k, cols k))
  have e2 := key (fun k => (rows (buchholzCyclicSucc k), cols k))
  unfold rademacherSign
  rw [e1, e2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [← pow_add]
  rfl

lemma E_sign {ι : Type*} [Fintype ι] [DecidableEq ι] (mult : ι → ℕ) :
    ((1 : ℝ) / 2) ^ Fintype.card ι *
        ∑ eps : Finset ι, ∏ c, (if c ∈ eps then (1 : ℝ) else -1) ^ (mult c)
      = if ∀ c, Even (mult c) then 1 else 0 := by
  have h1 : ∀ eps : Finset ι, ∏ c, (if c ∈ eps then (1 : ℝ) else -1) ^ (mult c) =
      (∏ c ∈ eps, (1 : ℝ)) * ∏ c ∈ epsᶜ, (-1 : ℝ) ^ (mult c) := by
    intro eps
    rw [← Finset.prod_mul_prod_compl eps]
    congr 1
    · exact Finset.prod_congr rfl (fun c hc => by simp [hc])
    · refine Finset.prod_congr rfl (fun c hc => ?_)
      rw [Finset.mem_compl] at hc
      simp [hc]
  simp_rw [h1]
  have h2 := Fintype.prod_add (fun _ : ι => (1 : ℝ)) (fun c => (-1 : ℝ) ^ (mult c))
  rw [← h2]
  split_ifs with h
  · have : ∀ c, (1 : ℝ) + (-1) ^ (mult c) = 2 := fun c => by
      rw [(h c).neg_one_pow]; norm_num
    simp only [this, Finset.prod_const, Finset.card_univ]
    rw [← mul_pow]; norm_num
  · obtain ⟨c, hc⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ c)]
    · ring
    · rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow]; norm_num

theorem link (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      = buchholzMatchedWalkSum n Omega p X := by
  unfold rademacherExpectation rademacherObservationWeight buchholzMatchedWalkSum
  simp_rw [trace_eq_walk n hn, walk_split, sign_prod_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun rows _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun cols _ => ?_)
  have hE := E_sign (buchholzEdgeMultiplicity rows cols)
  rw [show (∑ eps : Finset (Fin n1 × Fin n2), ((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
      (buchholzWalkProduct Omega p X rows cols *
        ∏ x : Fin n1 × Fin n2, (if x ∈ eps then (1 : ℝ) else -1) ^
          buchholzEdgeMultiplicity rows cols x)) =
      buchholzWalkProduct Omega p X rows cols *
        (((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
          ∑ eps : Finset (Fin n1 × Fin n2), ∏ x : Fin n1 × Fin n2,
            (if x ∈ eps then (1 : ℝ) else -1) ^ buchholzEdgeMultiplicity rows cols x) by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)]
  rw [hE]
  unfold buchholzWalkMatched
  split_ifs <;> simp

end Sol40809130

open MatrixCompletion in
theorem solution
    (n : Nat) (hn : 1 ≤ n)
    {n1 n2 : Nat} (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 < p)
    (X : RealMatrix n1 n2) :
    rademacherExpectation
        (fun eps =>
          Matrix.trace
            ((rademacherSampledMatrix Omega eps p X *
                (rademacherSampledMatrix Omega eps p X).transpose) ^ n))
      ≤ ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) *
          max ((sampledRowGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n))
              ((sampledColumnGramSchatten Omega p X (2 * n : ℝ)) ^ (2 * n)) := by
  rw [Sol40809130.link n hn Omega p X]
  exact SolE8b03350.matched_bound n hn Omega p hp X
