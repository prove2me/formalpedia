-- Prove2me | solution 1 for RiskUncSets.Distortion.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:02:52.319713+00:00
-- url     : https://prove2.me/submissions/ea9f934f-7390-466e-9fe9-77a3e5227474

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

set_option autoImplicit false

namespace P2db
open RiskUncSets.Distortion

section C1
variable {N : ℕ} {μ : (Fin N → ℝ) → ℝ}

lemma mu_zero (hc : IsCoherent μ) : μ 0 = 0 := by
  have := hc.2.2 0 0 le_rfl
  simpa using this

lemma mu_subadd (hc : IsCoherent μ) (X Y : Fin N → ℝ) : μ (X + Y) ≤ μ X + μ Y := by
  have h1 := hc.2.1 X Y (1/2) (by norm_num) (by norm_num)
  have h2 := hc.2.2 ((1/2:ℝ) • X + (1 - 1/2:ℝ) • Y) 2 (by norm_num)
  have e : (2:ℝ) • ((1/2:ℝ) • X + (1 - 1/2:ℝ) • Y) = X + Y := by
    ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e] at h2
  rw [h2]; linarith

lemma mu_perm (hL : IsLawInvariant (uniform N) μ) (X : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    μ (X ∘ σ) = μ X := by
  refine (hL _ _ ?_).symm
  intro t
  simp only [uniform, Finset.sum_filter, Function.comp]
  exact (Equiv.sum_comp σ (fun i => if X i ≤ t then (1 / (N:ℝ)) else 0)).symm

lemma como_of_mono {X Y : Fin N → ℝ} (hX : Monotone X) (hY : Monotone Y) : Comonotone X Y := by
  intro ω ω'
  rcases le_total ω ω' with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hX h]) (by linarith [hY h])
  · exact mul_nonneg (by linarith [hX h]) (by linarith [hY h])

noncomputable def ind (N k : ℕ) : Fin N → ℝ := fun i => if k ≤ (i:ℕ) then 1 else 0

lemma ind_mono (k : ℕ) : Monotone (ind N k) := by
  intro i j hij
  have h' : (i:ℕ) ≤ j := Fin.le_iff_val_le_val.mp hij
  simp only [ind]
  split_ifs with h1 h2
  all_goals (try norm_num)
  all_goals omega

lemma mu_sum (hc : IsCoherent μ) (hco : IsComonotonic μ) (w : ℕ → ℝ) :
    ∀ s : Finset ℕ, (∀ k ∈ s, 0 ≤ w k) →
      μ (fun i => ∑ k ∈ s, w k * ind N k i) = ∑ k ∈ s, w k * μ (ind N k) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact mu_zero hc
  | insert a s ha ih =>
    intro hw
    have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self a s)
    have hws : ∀ k ∈ s, 0 ≤ w k := fun k hk => hw k (Finset.mem_insert_of_mem hk)
    have hsplit : (fun i => ∑ k ∈ insert a s, w k * ind N k i) =
        (w a • ind N a) + (fun i => ∑ k ∈ s, w k * ind N k i) := by
      ext i; simp [Finset.sum_insert ha, smul_eq_mul]
    have hm1 : Monotone (w a • ind N a) := by
      intro i j h
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (ind_mono a h) hwa
    have hm2 : Monotone (fun i => ∑ k ∈ s, w k * ind N k i) := by
      intro i j h
      exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (ind_mono k h) (hws k hk)
    rw [hsplit, hco _ _ (como_of_mono hm1 hm2), hc.2.2 _ _ hwa, ih hws, Finset.sum_insert ha]

lemma tele (g : ℕ → ℝ) (k : ℕ) : ∀ M, k ≤ M →
    ∑ i ∈ Finset.range M, (g i - g (i+1)) * (if k ≤ i then 1 else 0) = g k - g M := by
  intro M hM
  induction M with
  | zero =>
    have : k = 0 := by omega
    subst this; simp
  | succ M ih =>
    rcases Nat.lt_or_ge M k with h | h
    · have hk : k = M + 1 := by omega
      subst hk
      rw [Finset.sum_eq_zero]
      · simp
      intro i hi
      rw [Finset.mem_range] at hi
      rw [if_neg (by omega)]; ring
    · rw [Finset.sum_range_succ, ih h, if_pos h]; ring

/-- the generator values `g k = -μ(1_{i ≥ k})` -/
noncomputable def gg (μ : (Fin N → ℝ) → ℝ) (k : ℕ) : ℝ := -μ (ind N k)

lemma ind_ge (k : ℕ) (hk : N ≤ k) : ind N k = 0 := by
  ext i; simp only [ind, Pi.zero_apply]; rw [if_neg (by omega)]

lemma gg_ge (hc : IsCoherent μ) (k : ℕ) (hk : N ≤ k) : gg μ k = 0 := by
  simp [gg, ind_ge k hk, mu_zero hc]

lemma gg_zero (hc : IsCoherent μ) : gg μ 0 = 1 := by
  have h := hc.1.2 0 1
  have e : (fun i : Fin N => (0 : Fin N → ℝ) i + 1) = ind N 0 := by
    ext i; simp [ind]
  rw [e, mu_zero hc] at h
  simp [gg, h]

lemma sum_q_ind (hc : IsCoherent μ) (k : ℕ) (hk : k ≤ N) :
    ∑ i : Fin N, (gg μ i - gg μ (i+1)) * ind N k i = gg μ k := by
  have := Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (gg μ i - gg μ (i+1)) * (if k ≤ i then (1:ℝ) else 0)) N
  simp only [ind]
  rw [this, tele _ k N hk, gg_ge hc N le_rfl, sub_zero]

lemma partial_tele (w z : ℕ → ℝ) (hw0 : w 0 = 0) (hw : ∀ k, 1 ≤ k → w k = z k - z (k-1)) :
    ∀ j, ∑ k ∈ Finset.range (j+1), w k = z j - z 0 := by
  intro j
  induction j with
  | zero => simp [hw0]
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, hw (j+1) (by omega)]
    simp

lemma mu_mono_rep (hN : 0 < N) (hc : IsCoherent μ) (hco : IsComonotonic μ)
    (Z : Fin N → ℝ) (hZ : Monotone Z) :
    μ Z = -∑ i : Fin N, (gg μ i - gg μ (i+1)) * Z i := by
  set z : ℕ → ℝ := fun m => if h : m < N then Z ⟨m, h⟩ else 0 with hzdef
  set w : ℕ → ℝ := fun k => if k = 0 then 0 else z k - z (k-1) with hwdef
  have hzZ : ∀ i : Fin N, z i = Z i := by
    intro i; simp [hzdef, i.isLt]
  have hwnn : ∀ k ∈ Finset.range N, 0 ≤ w k := by
    intro k hk
    rw [Finset.mem_range] at hk
    simp only [hwdef]
    split_ifs with h0
    · exact le_rfl
    · have h1 : k - 1 < N := by omega
      simp only [hzdef, dif_pos hk, dif_pos h1, sub_nonneg]
      apply hZ
      rw [Fin.le_iff_val_le_val]; simp
  set Z0 : ℝ := Z ⟨0, hN⟩ with hZ0
  have hdec : ∀ i : Fin N, Z i = (∑ k ∈ Finset.range N, w k * ind N k i) + Z0 := by
    intro i
    have e1 : ∑ k ∈ Finset.range N, w k * ind N k i = ∑ k ∈ Finset.range ((i:ℕ)+1), w k := by
      simp only [ind, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; have := i.isLt; omega
    rw [e1, partial_tele w z (by simp [hwdef]) (fun k hk => by simp [hwdef]; omega) i, hzZ i]
    have : z 0 = Z0 := by simp [hzdef, hZ0, hN]
    rw [this]; ring
  have hZeq : Z = fun i => (fun i => ∑ k ∈ Finset.range N, w k * ind N k i) i + Z0 := by
    ext i; exact hdec i
  have hL : μ Z = ∑ k ∈ Finset.range N, w k * μ (ind N k) - Z0 := by
    rw [hZeq, hc.1.2, mu_sum hc hco w _ hwnn]
  rw [hL]
  have hR : ∑ i : Fin N, (gg μ i - gg μ (i+1)) * Z i =
      ∑ k ∈ Finset.range N, w k * gg μ k + Z0 := by
    simp_rw [hdec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : ∑ i : Fin N, (gg μ i - gg μ (i+1)) * Z0 = Z0 := by
      rw [← Finset.sum_mul]
      have := sum_q_ind hc 0 (Nat.zero_le N)
      rw [gg_zero hc] at this
      have e : ∑ i : Fin N, (gg μ i - gg μ (i+1)) = 1 := by
        rw [← this]; congr 1; ext i; simp [ind]
      rw [e, one_mul]
    rw [h1, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have := sum_q_ind hc k hk.le
    rw [← this, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hR]
  simp only [gg]
  have : ∑ k ∈ Finset.range N, w k * -μ (ind N k) = -∑ k ∈ Finset.range N, w k * μ (ind N k) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  rw [this]; ring

lemma gg_anti_step (hc : IsCoherent μ) (m : ℕ) : gg μ (m+1) ≤ gg μ m := by
  simp only [gg, neg_le_neg_iff]
  apply hc.1.1
  intro i
  simp only [ind]
  split_ifs with h1 h2
  all_goals (try norm_num)
  all_goals omega

lemma q_anti_step (hN : 0 < N) (hc : IsCoherent μ) (hco : IsComonotonic μ)
    (hL : IsLawInvariant (uniform N) μ) (m : ℕ) :
    gg μ (m+1) - gg μ (m+1+1) ≤ gg μ m - gg μ (m+1) := by
  by_cases hm : m + 2 ≤ N
  · -- convexity via a swap
    have hm0 : m < N := by omega
    have hm1 : m + 1 < N := by omega
    let s : Equiv.Perm (Fin N) := Equiv.swap ⟨m, hm0⟩ ⟨m+1, hm1⟩
    have hsum : ind N m + ind N (m+2) = ind N (m+1) + ind N (m+1) ∘ s := by
      ext i
      simp only [Pi.add_apply, Function.comp, s]
      by_cases ha : i = ⟨m, hm0⟩
      · subst ha; rw [Equiv.swap_apply_left]; simp [ind]
      · by_cases hb : i = ⟨m+1, hm1⟩
        · subst hb; rw [Equiv.swap_apply_right]; simp [ind]
        · rw [Equiv.swap_apply_of_ne_of_ne ha hb]
          have ha' : (i:ℕ) ≠ m := fun h => ha (Fin.ext h)
          have hb' : (i:ℕ) ≠ m + 1 := fun h => hb (Fin.ext h)
          simp only [ind]
          split_ifs
          all_goals (try norm_num)
          all_goals omega
    have hco' := hco _ _ (como_of_mono (ind_mono (N := N) m) (ind_mono (N := N) (m+2)))
    have hsub := mu_subadd hc (ind N (m+1)) (ind N (m+1) ∘ s)
    rw [mu_perm hL, ← hsum, hco'] at hsub
    simp only [gg]
    have e : m + 1 + 1 = m + 2 := rfl
    rw [e]
    linarith
  · have h1 : gg μ (m+1+1) = 0 := gg_ge hc _ (by omega)
    have h2 : gg μ (m+1) = 0 := gg_ge hc _ (by omega)
    rw [h1, h2]; have := gg_anti_step hc m; linarith

theorem rep (hN : 0 < N) (hμ : IsDistortion (uniform N) μ) :
    ∃ q ∈ restrictedSimplex N, ∀ X, μ X = muQ q X := by
  obtain ⟨hc, hco, hL⟩ := hμ
  refine ⟨fun i => gg μ i - gg μ (i+1), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; have := gg_anti_step hc i; simp only; linarith
  · have := sum_q_ind hc 0 (Nat.zero_le N)
    rw [gg_zero hc] at this
    rw [← this]; congr 1; ext i; simp [ind]
  · have hA : Antitone (fun m : ℕ => gg μ m - gg μ (m+1)) :=
      antitone_nat_of_succ_le (fun m => q_anti_step hN hc hco hL m)
    intro i j hij
    exact hA (Fin.le_iff_val_le_val.mp hij)
  · intro X
    rw [← mu_perm hL X (Tuple.sort X), mu_mono_rep hN hc hco _ (Tuple.monotone_sort X), muQ]
    rfl

end C1

section Dual
variable {N : ℕ}

/-- explicit dual potentials for the sorted assignment problem -/
noncomputable def FF (q' d' : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => FF q' d' m + q' (m+1) * (d' (m+1) - d' m)

lemma FF_le (q' d' : ℕ → ℝ) (M : ℕ)
    (hq : ∀ m n, m ≤ n → n < M → q' n ≤ q' m)
    (hd : ∀ m n, m ≤ n → n < M → d' m ≤ d' n) :
    ∀ i k, i < M → k < M → FF q' d' k - FF q' d' i ≤ q' i * (d' k - d' i) := by
  intro i k hi hk
  rcases le_total i k with h | h
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    induction t with
    | zero => simp
    | succ t ih =>
      have ih' := ih (by omega) (by omega)
      have e : i + (t+1) = (i + t) + 1 := by ring
      rw [e, FF]
      have h1 := hq i (i+t+1) (by omega) (by omega)
      have h2 := hd (i+t) (i+t+1) (by omega) (by omega)
      nlinarith
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
    induction t with
    | zero => simp
    | succ t ih =>
      have ih' := ih (by omega) (by omega)
      have e : k + (t+1) = (k + t) + 1 := by ring
      rw [e, FF]
      have h1 := hq (k+t) (k+t+1) (by omega) (by omega)
      have h2 := hd (k+t) (k+t+1) (by omega) (by omega)
      have h3 := hd k (k+t) (by omega) (by omega)
      have h4 : q' (k+t) * (d' k - d' (k+t)) ≤ q' (k+t+1) * (d' k - d' (k+t)) := by nlinarith
      nlinarith

end Dual

section Main
variable {N : ℕ}

lemma perm_vec_dot {n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    (∑ i, q (σ i) • a i) ⬝ᵥ x = ∑ i, q (σ i) * (a i ⬝ᵥ x) := by
  rw [sum_dotProduct]
  simp [smul_dotProduct]

lemma hull_iff {n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) :
    (∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x) ↔
      ∀ σ : Equiv.Perm (Fin N), b ≤ ∑ i, q (σ i) * (a i ⬝ᵥ x) := by
  constructor
  · intro h σ
    rw [← perm_vec_dot]
    exact h _ (subset_convexHull ℝ _ ⟨σ, rfl⟩)
  · intro h a' ha'
    have hconv : Convex ℝ {v : Fin n → ℝ | b ≤ v ⬝ᵥ x} := by
      intro u hu v hv s t hs ht hst
      simp only [Set.mem_setOf_eq] at hu hv ⊢
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      have e1 := mul_le_mul_of_nonneg_left hu hs
      have e2 := mul_le_mul_of_nonneg_left hv ht
      have e3 : s * b + t * b = b := by rw [← add_mul, hst, one_mul]
      linarith
    have hsub : Set.range (fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i) ⊆
        {v : Fin n → ℝ | b ≤ v ⬝ᵥ x} := by
      rintro _ ⟨σ, rfl⟩
      simp only [Set.mem_setOf_eq]
      rw [perm_vec_dot]; exact h σ
    exact convexHull_min hsub hconv ha'

/-- with `q` antitone and `c ∘ τ` monotone, the sorted pairing is the minimum -/
lemma rearr (q c : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) (hq : Antitone q) (hd : Monotone (c ∘ τ))
    (σ : Equiv.Perm (Fin N)) :
    ∑ k, q k * c (τ k) ≤ ∑ i, q (σ i) * c i := by
  have h1 : ∑ i, q (σ i) * c i = ∑ k, q (σ (τ k)) * c (τ k) :=
    (Equiv.sum_comp τ (fun i => q (σ i) * c i)).symm
  rw [h1]
  have := (hq.antivary hd).sum_mul_le_sum_comp_perm_mul (σ := τ.trans σ)
  simpa [Function.comp, Equiv.trans_apply] using this

lemma dual_exists (q c : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) (hq : Antitone q)
    (hd : Monotone (c ∘ τ)) :
    ∃ y₁ y₂ : Fin N → ℝ, ∑ i, y₁ i + ∑ j, y₂ j = ∑ k, q k * c (τ k) ∧
      ∀ i j, y₁ i + y₂ j ≤ q i * c j := by
  let q' : ℕ → ℝ := fun m => if h : m < N then q ⟨m, h⟩ else 0
  let d' : ℕ → ℝ := fun m => if h : m < N then c (τ ⟨m, h⟩) else 0
  have hq'i : ∀ i : Fin N, q' i = q i := fun i => by simp [q', i.isLt]
  have hd'i : ∀ i : Fin N, d' i = c (τ i) := fun i => by simp [d', i.isLt]
  have hq' : ∀ m n, m ≤ n → n < N → q' n ≤ q' m := by
    intro m n hmn hn
    have hm : m < N := by omega
    simp only [q', dif_pos hn, dif_pos hm]
    exact hq (Fin.le_iff_val_le_val.mpr hmn)
  have hd' : ∀ m n, m ≤ n → n < N → d' m ≤ d' n := by
    intro m n hmn hn
    have hm : m < N := by omega
    simp only [d', dif_pos hn, dif_pos hm]
    exact hd (Fin.le_iff_val_le_val.mpr hmn)
  refine ⟨fun i => q i * c (τ i) - FF q' d' i, fun j => FF q' d' (τ.symm j), ?_, ?_⟩
  · have : ∑ j, FF q' d' (τ.symm j) = ∑ i : Fin N, FF q' d' i :=
      Equiv.sum_comp τ.symm (fun i : Fin N => FF q' d' i)
    rw [this, Finset.sum_sub_distrib]; ring
  · intro i j
    have key := FF_le q' d' N hq' hd' i (τ.symm j) i.isLt (τ.symm j).isLt
    rw [hq'i, hd'i, hd'i, Equiv.apply_symm_apply] at key
    simp only
    nlinarith

end Main

end P2db

open P2db in
open RiskUncSets.Distortion in
theorem solution {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ)
    (hμ : IsDistortion (uniform N) μ) :
    ∃ q ∈ restrictedSimplex N, (∀ X, μ X = muQ q X) ∧
      ∀ (n : ℕ) (a : Fin N → Fin n → ℝ) (b : ℝ),
        {x : Fin n → ℝ | μ (fun i => a i ⬝ᵥ x - b) ≤ 0} =
            {x | ∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x} ∧
          {x : Fin n → ℝ | ∀ a' ∈ permutohull q a, b ≤ a' ⬝ᵥ x} =
            {x | ∃ y₁ y₂ : Fin N → ℝ, b ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
              ∀ i j, y₁ i + y₂ j ≤ q i * (a j ⬝ᵥ x)} := by
  obtain ⟨q, hq, hrep⟩ := rep hN hμ
  have hqa : Antitone q := hq.2
  have hq1 : ∑ i, q i = 1 := hq.1.2
  refine ⟨q, hq, hrep, fun n a b => ⟨?_, ?_⟩⟩
  · ext x
    simp only [Set.mem_setOf_eq]
    rw [hull_iff]
    set X : Fin N → ℝ := fun i => a i ⬝ᵥ x - b with hX
    set c : Fin N → ℝ := fun i => a i ⬝ᵥ x with hc
    set τ := Tuple.sort X
    have hd : Monotone (c ∘ τ) := by
      intro i j h
      have := Tuple.monotone_sort X h
      simp only [Function.comp, hX] at this
      simp only [Function.comp, hc]; linarith
    have hmu : μ X = b - ∑ k, q k * c (τ k) := by
      rw [hrep, muQ]
      simp only [hX, hc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1]
      ring
    rw [hmu]
    constructor
    · intro h σ
      have := rearr q c τ hqa hd σ
      simp only [hc] at this
      linarith
    · intro h
      have := h τ.symm
      have e : ∑ i, q (τ.symm i) * c i = ∑ k, q k * c (τ k) := by
        rw [← Equiv.sum_comp τ (fun i => q (τ.symm i) * c i)]
        simp
      simp only [hc] at e
      linarith
  · ext x
    simp only [Set.mem_setOf_eq]
    rw [hull_iff]
    set c : Fin N → ℝ := fun i => a i ⬝ᵥ x with hc
    constructor
    · intro h
      set τ := Tuple.sort c
      have hd : Monotone (c ∘ τ) := Tuple.monotone_sort c
      obtain ⟨y₁, y₂, hsum, hle⟩ := dual_exists q c τ hqa hd
      refine ⟨y₁, y₂, ?_, hle⟩
      rw [hsum]
      have := h τ.symm
      have e : ∑ i, q (τ.symm i) * c i = ∑ k, q k * c (τ k) := by
        rw [← Equiv.sum_comp τ (fun i => q (τ.symm i) * c i)]
        simp
      simp only [hc] at e
      linarith
    · rintro ⟨y₁, y₂, hb, hle⟩ σ
      have h1 : ∑ i, (y₁ (σ i) + y₂ i) ≤ ∑ i, q (σ i) * (a i ⬝ᵥ x) :=
        Finset.sum_le_sum fun i _ => hle (σ i) i
      rw [Finset.sum_add_distrib, Equiv.sum_comp σ y₁] at h1
      linarith
