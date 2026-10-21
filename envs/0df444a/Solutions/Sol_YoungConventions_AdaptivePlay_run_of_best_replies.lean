-- Prove2me | solution 1 for YoungConventions.AdaptivePlay.run_of_best_replies
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:31:31.132924+00:00
-- url     : https://prove2.me/submissions/738b8cb6-c60e-42f5-841f-fec0e6c0f204

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_IsBestReplyDistribution
import Definitions.Def_YoungConventions_AdaptivePlay_adaptivePlay

set_option autoImplicit false
open YoungConventions.AdaptivePlay

theorem yca_P_nonneg {ι : Type*} [Fintype ι] {S : ι → Type*} [∀ i, Fintype (S i)] {m : ℕ} [NeZero m]
    (p : ∀ i, History S m → S i → ℝ) (hp0 : ∀ i h x, 0 ≤ p i h x) (h h' : History S m) :
    0 ≤ adaptivePlay p h h' := by
  unfold adaptivePlay
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => hp0 i h _)
  · exact le_rfl

theorem yca_P_rowsum {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] {m : ℕ} [NeZero m]
    (p : ∀ i, History S m → S i → ℝ) (hp1 : ∀ i h, ∑ x, p i h x = 1) (h : History S m) :
    ∑ h', adaptivePlay p h h' = 1 := by
  classical
  have hm : 0 < m := NeZero.pos m
  let L : Fin m := ⟨m - 1, Nat.sub_lt hm Nat.one_pos⟩
  let φ : (∀ i, S i) → History S m :=
    fun s t => if ht : t.val + 1 < m then h ⟨t.val + 1, ht⟩ else s
  have hφL : ∀ s, φ s L = s := by
    intro s; simp only [φ, L]; rw [dif_neg (by omega)]
  have hinj : Function.Injective φ := fun s s' hss => by
    have := congrFun hss L
    rwa [hφL, hφL] at this
  have hsucc : ∀ h', IsSuccessor h h' ↔ h' = φ (h' L) := by
    intro h'
    constructor
    · intro hs
      funext t
      by_cases ht : t.val + 1 < m
      · simp only [φ, dif_pos ht]; exact hs t ht
      · have : t = L := by apply Fin.ext; simp only [L]; omega
        subst this
        exact (hφL _).symm
    · intro e t ht
      have := congrFun e t
      rw [this]
      simp only [φ, dif_pos ht]
  calc ∑ h', adaptivePlay p h h'
      = ∑ h' ∈ Finset.univ.filter (fun h' => IsSuccessor h h'), ∏ i, p i h (h' L i) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun h' _ => ?_)
        by_cases hs : IsSuccessor h h' <;> simp [adaptivePlay, hs, L]
    _ = ∑ h' ∈ Finset.univ.image φ, ∏ i, p i h (h' L i) := by
        congr 1
        ext h'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hs; exact ⟨h' L, ((hsucc h').mp hs).symm⟩
        · rintro ⟨s, rfl⟩; exact (hsucc _).mpr (by rw [hφL])
    _ = ∑ s : ∀ i, S i, ∏ i, p i h (φ s L i) :=
        Finset.sum_image hinj.injOn
    _ = ∑ s : ∀ i, S i, ∏ i, p i h (s i) := by simp_rw [hφL]
    _ = ∏ i, ∑ x, p i h x := (Fintype.prod_sum (fun i x => p i h x)).symm
    _ = 1 := by simp [hp1 _ h]

theorem yca_stoch_pow {H : Type*} [Fintype H] [DecidableEq H] (A : Matrix H H ℝ)
    (h0 : ∀ a b, 0 ≤ A a b) (h1 : ∀ a, ∑ b, A a b = 1) :
    ∀ n : ℕ, (∀ a b, 0 ≤ (A ^ n) a b) ∧ ∀ a, ∑ b, (A ^ n) a b = 1 := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [pow_zero, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [Matrix.mul_apply]
      exact Finset.sum_nonneg (fun c _ => mul_nonneg (ih.1 a c) (h0 c b))
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, h1, mul_one]
      exact ih.2 a


theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : 2 * k ≤ m + 1)
    (p : ∀ i, History S m → S i → ℝ) (hp : IsBestReplyDistribution u k p)
    (h : History S m) (s : ∀ i, S i)
    (hs : ∀ i, IsSampleBestReply u h (Finset.univ.filter fun t : Fin m => m ≤ t.val + k) i (s i)) :
    0 < (adaptivePlay p ^ k) h
      (fun t => if ht : t.val + k < m then h ⟨t.val + k, ht⟩ else s) := by
  have hm : 0 < m := NeZero.pos m
  have hP0 := yca_P_nonneg p hp.1
  have hP1 := yca_P_rowsum p hp.2.1
  have hst := yca_stoch_pow (adaptivePlay p) hP0 hP1
  let g : ℕ → History S m := fun j t => if ht : t.val + j < m then h ⟨t.val + j, ht⟩ else s
  have hg_pos : ∀ j (t : Fin m) (ht : t.val + j < m), g j t = h ⟨t.val + j, ht⟩ :=
    fun j t ht => dif_pos ht
  have hg_neg : ∀ j (t : Fin m), ¬ t.val + j < m → g j t = s := fun j t ht => dif_neg ht
  have hg0 : g 0 = h := by
    funext t
    rw [hg_pos 0 t t.isLt]
    rfl
  set K0 : Finset (Fin m) := Finset.univ.filter (fun t : Fin m => m ≤ t.val + k) with hK0
  have hK0eq : K0 = Finset.Ici (⟨m - k, by omega⟩ : Fin m) := by
    ext t
    simp only [hK0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def, Fin.val_mk]
    omega
  have hK0card : K0.card = k := by
    rw [hK0eq, Fin.card_Ici]
    show m - (m - k) = k
    omega
  -- samples of the shifted histories
  have hsample : ∀ j, j < k → ∀ i, 0 < p i (g j) (s i) := by
    intro j hj i
    rw [hp.2.2 i (g j) (s i)]
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin m → Fin m, ∀ t : Fin m, ∀ ht : t.val + j < m,
        (ψ t).val = t.val + j :=
      ⟨fun t => if ht : t.val + j < m then ⟨t.val + j, ht⟩ else t, by intro t ht; simp [ht]⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin m → Fin m, ∀ t : Fin m, j ≤ t.val → (ρ t).val = t.val - j :=
      ⟨fun t => if ht : j ≤ t.val then ⟨t.val - j, by have := t.isLt; omega⟩ else t,
        by intro t ht; simp [ht]⟩
    set Kj : Finset (Fin m) :=
      Finset.univ.filter (fun t : Fin m => m ≤ t.val + j + k ∧ t.val + j < m) with hKj
    have hsum : ∀ F : (∀ i, S i) → ℝ, ∑ t ∈ Kj, F (g j t) = ∑ t ∈ K0, F (h t) := by
      intro F
      refine Finset.sum_nbij' ψ ρ ?_ ?_ ?_ ?_ ?_
      · intro t ht
        simp only [hKj, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        simp only [hK0, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hψ t ht.2]
        omega
      · intro t' ht'
        simp only [hK0, Finset.mem_filter, Finset.mem_univ, true_and] at ht'
        have hlt := t'.isLt
        have hj' : j ≤ t'.val := by omega
        simp only [hKj, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hρ t' hj']
        constructor <;> omega
      · intro t ht
        simp only [hKj, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        apply Fin.ext
        have h1 := hψ t ht.2
        have h2 := hρ (ψ t) (by omega)
        omega
      · intro t' ht'
        simp only [hK0, Finset.mem_filter, Finset.mem_univ, true_and] at ht'
        have hlt := t'.isLt
        have hj' : j ≤ t'.val := by omega
        apply Fin.ext
        have h1 := hρ t' hj'
        have h2 := hψ (ρ t') (by omega)
        omega
      · intro t ht
        simp only [hKj, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        rw [hg_pos j t ht.2]
        congr 2
        apply Fin.ext
        rw [hψ t ht.2]
    have hcard : Kj.card = k := by
      have h1 := hsum (fun _ => (1 : ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
      have h2 : Kj.card = K0.card := by exact_mod_cast h1
      rw [h2, hK0card]
    refine ⟨Kj, hcard, ?_⟩
    intro y
    have e1 : ∑ t ∈ Kj, u i (Function.update (g j t) i y) =
        ∑ t ∈ K0, u i (Function.update (h t) i y) :=
      hsum (fun z => u i (Function.update z i y))
    have e2 : ∑ t ∈ Kj, u i (Function.update (g j t) i (s i)) =
        ∑ t ∈ K0, u i (Function.update (h t) i (s i)) :=
      hsum (fun z => u i (Function.update z i (s i)))
    rw [e1, e2]
    exact hs i y
  have hstep : ∀ j, j < k → 0 < adaptivePlay p (g j) (g (j + 1)) := by
    intro j hj
    have hsucc : IsSuccessor (g j) (g (j + 1)) := by
      intro t ht
      by_cases hc : t.val + (j + 1) < m
      · rw [hg_pos (j + 1) t hc, hg_pos j ⟨t.val + 1, ht⟩ (by show t.val + 1 + j < m; omega)]
        exact congrArg h (Fin.ext (by show t.val + (j + 1) = t.val + 1 + j; omega))
      · rw [hg_neg (j + 1) t hc, hg_neg j ⟨t.val + 1, ht⟩ (by show ¬ (t.val + 1 + j < m); omega)]
    have hL : g (j + 1) ⟨m - 1, Nat.sub_lt (NeZero.pos m) Nat.one_pos⟩ = s :=
      hg_neg (j + 1) _ (by show ¬ (m - 1 + (j + 1) < m); omega)
    unfold adaptivePlay
    rw [if_pos hsucc, hL]
    exact Finset.prod_pos (fun i _ => hsample j hj i)
  have hchain : ∀ j, j ≤ k → 0 < (adaptivePlay p ^ j) h (g j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [pow_zero, Matrix.one_apply, hg0, if_pos rfl]
      exact one_pos
    | succ j ih =>
      intro hj
      rw [pow_succ, Matrix.mul_apply]
      have hle : (adaptivePlay p ^ j) h (g j) * adaptivePlay p (g j) (g (j + 1)) ≤
          ∑ c, (adaptivePlay p ^ j) h c * adaptivePlay p c (g (j + 1)) :=
        Finset.single_le_sum (f := fun c => (adaptivePlay p ^ j) h c * adaptivePlay p c (g (j + 1)))
          (fun c _ => mul_nonneg ((hst j).1 h c) (hP0 c _)) (Finset.mem_univ (g j))
      exact lt_of_lt_of_le (mul_pos (ih (by omega)) (hstep j (by omega))) hle
  exact hchain k le_rfl
