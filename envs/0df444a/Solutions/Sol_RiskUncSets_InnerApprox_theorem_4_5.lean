-- Prove2me | solution 1 for RiskUncSets.InnerApprox.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:19:34.698251+00:00
-- url     : https://prove2.me/submissions/29b341db-1e0a-4712-aff9-1f3663122528

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting

set_option autoImplicit false

noncomputable section

namespace Pb72
open RiskUncSets.InnerApprox

lemma perm_vec_dot {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    (∑ i, q (σ i) • a i) ⬝ᵥ x = ∑ i, q (σ i) * (a i ⬝ᵥ x) := by
  rw [sum_dotProduct]
  simp [smul_dotProduct]

lemma hull_iff {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (b : ℝ) (x : Fin n → ℝ) :
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

lemma sub_iff {N n m : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) :
    permutohull q a ⊆ polytope u v ↔
      ∀ k (σ : Equiv.Perm (Fin N)), v k ≤ ∑ i, q (σ i) * (a i ⬝ᵥ u k) := by
  constructor
  · intro h k
    apply (hull_iff q a (v k) (u k)).mp
    intro a' ha'
    rw [dotProduct_comm]
    exact h ha' k
  · intro h x hx k
    show v k ≤ u k ⬝ᵥ x
    rw [dotProduct_comm]
    exact (hull_iff q a (v k) (u k)).mpr (h k) x hx

/-- with `q` antitone and `c ∘ τ` monotone, explicit dual potentials -/
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

lemma dual_exists {N : ℕ} (q c : Fin N → ℝ) (τ : Equiv.Perm (Fin N)) (hq : Antitone q)
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

/-- vertex conditions at an antitone mixture give LP (15) feasibility -/
lemma feas {N n m : ℕ} (qh : Fin N → ℝ) (hanti : Antitone qh) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (h : ∀ k (σ : Equiv.Perm (Fin N)), v k ≤ ∑ i, mix qh lam (σ i) * (a i ⬝ᵥ u k)) :
    LP15Feasible qh a u v lam := by
  have hqa : Antitone (mix qh lam) := by
    intro i j hij
    simp only [mix]
    have := hanti hij
    nlinarith
  have hk : ∀ k, ∃ y₁ y₂ : Fin N → ℝ, v k ≤ ∑ i, y₁ i + ∑ j, y₂ j ∧
      ∀ i j, y₁ i + y₂ j ≤ (u k ⬝ᵥ a j) * mix qh lam i := by
    intro k
    set c : Fin N → ℝ := fun j => u k ⬝ᵥ a j with hc
    set τ := Tuple.sort c
    have hd : Monotone (c ∘ τ) := Tuple.monotone_sort c
    obtain ⟨y₁, y₂, hsum, hle⟩ := dual_exists (mix qh lam) c τ hqa hd
    refine ⟨y₁, y₂, ?_, fun i j => ?_⟩
    · rw [hsum]
      have h1 := h k τ.symm
      have e : ∑ i, mix qh lam (τ.symm i) * c i = ∑ k, mix qh lam k * c (τ k) := by
        rw [← Equiv.sum_comp τ (fun i => mix qh lam (τ.symm i) * c i)]
        simp
      have e2 : ∑ i, mix qh lam (τ.symm i) * (a i ⬝ᵥ u k) =
          ∑ i, mix qh lam (τ.symm i) * c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hc, dotProduct_comm]
      linarith
    · have := hle i j
      simp only [hc] at this
      linarith
  choose s t hs using hk
  refine ⟨mix qh lam, s, t, rfl, fun k => ?_, fun k i j => (hs k).2 i j⟩
  rw [Finset.sum_add_distrib]
  exact (hs k).1

lemma restricted_iff {N : ℕ} (hN : 0 < N) (qh : Fin N → ℝ)
    (hqh : qh ∈ restrictedSimplex N) (hmin : (N : ℝ) * (⨅ i, qh i) < 1)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    mix qh lam ∈ restrictedSimplex N ↔ lam ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i) := by
  obtain ⟨⟨hnn, hsum⟩, hanti⟩ := hqh
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set m := ⨅ i, qh i with hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < 1 - (N : ℝ) * m := by linarith
  have hmle : ∀ i, m ≤ qh i := fun i => ciInf_le (Set.finite_range qh).bddBelow i
  obtain ⟨i0, hi0⟩ : ∃ i0, qh i0 = m := by
    obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := qh)
    exact ⟨i0, hi0⟩
  have key : lam ≤ 1 / (1 - (N : ℝ) * m) ↔ 0 ≤ lam * m + (1 - lam) * (1 / (N : ℝ)) := by
    rw [le_div_iff₀ hpos]
    have h1 : lam * m + (1 - lam) * (1 / (N : ℝ)) = (1 - lam * (1 - (N : ℝ) * m)) / N := by
      field_simp
      ring
    rw [h1, div_nonneg_iff]
    constructor
    · intro h; left; exact ⟨by linarith, hNpos.le⟩
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · linarith
      · linarith
  rw [key]
  constructor
  · rintro ⟨⟨hnn', _⟩, _⟩
    have := hnn' i0
    simp only [mix] at this
    rw [hi0] at this
    exact this
  · intro h
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · simp only [mix]
      have := hmle i
      nlinarith
    · simp only [mix]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp
      ring
    · intro i j hij
      simp only [mix]
      have := hanti hij
      nlinarith

end Pb72

open Pb72 in
open RiskUncSets.InnerApprox in
theorem solution {N n m : ℕ} (hN : 0 < N) (qh : Fin N → ℝ)
    (hqh : qh ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (u : Fin m → Fin n → ℝ) (v : Fin m → ℝ) (hmean : sampleMean a ∈ polytope u v)
    (lamStar : ℝ) (hopt : IsGreatest {lam | LP15Feasible qh a u v lam} lamStar) :
    permutohull (mix qh lamStar) a ⊆ polytope u v ∧
    (∀ lam : ℝ, permutohull (mix qh lam) a ⊆ polytope u v →
      permutohull (mix qh lam) a ⊆ permutohull (mix qh lamStar) a) ∧
    ((N : ℝ) * (⨅ i, qh i) < 1 →
      (mix qh lamStar ∈ restrictedSimplex N ↔
        lamStar ≤ 1 / (1 - (N : ℝ) * ⨅ i, qh i))) := by
  obtain ⟨hres, ρ, hρ⟩ := hqh
  have hanti : Antitone qh := hres.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- reflection: mix at -lam is mix at lam composed with ρ
  have hrefl : ∀ (lam : ℝ) (j : Fin N), mix qh (-lam) j = mix qh lam (ρ j) := by
    intro lam j
    have : qh j = 2 / (N : ℝ) - qh (ρ j) := congrFun hρ j
    simp only [mix]
    linear_combination (-lam) * this
  -- conjunct 1: weak duality
  have hc1 : permutohull (mix qh lamStar) a ⊆ polytope u v := by
    obtain ⟨q, s, t, hq, h1, h2⟩ := hopt.1
    rw [sub_iff]
    intro k σ
    have hle : ∑ i, (s k (σ i) + t k i) ≤ ∑ i, mix qh lamStar (σ i) * (a i ⬝ᵥ u k) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := h2 k (σ i) i
      rw [hq, dotProduct_comm] at this
      linarith
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ (s k)] at hle
    have := h1 k
    rw [Finset.sum_add_distrib] at this
    linarith
  -- 0 ≤ lamStar: lam = 0 is feasible
  have hzero : 0 ≤ lamStar := by
    apply hopt.2
    refine ⟨mix qh 0, fun _ _ => 0, fun k j => (u k ⬝ᵥ a j) * (1 / (N : ℝ)), rfl, ?_, ?_⟩
    · intro k
      have hk := hmean k
      simp only [sampleMean, dotProduct_sum, dotProduct_smul, smul_eq_mul] at hk
      simp only [zero_add]
      have e : ∑ i, (u k ⬝ᵥ a i) * (1 / (N : ℝ)) = ∑ i, 1 / (N : ℝ) * (u k ⬝ᵥ a i) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e]; exact hk
    · intro k i j
      simp only [mix]
      ring_nf
      exact le_refl _
  refine ⟨hc1, ?_, fun hmin => restricted_iff hN qh hres hmin lamStar hzero⟩
  -- conjunct 2
  intro lam hlam
  have hv := (sub_iff _ a u v).mp hlam
  -- vertex conditions at -lam
  have hvneg : ∀ k (σ : Equiv.Perm (Fin N)),
      v k ≤ ∑ i, mix qh (-lam) (σ i) * (a i ⬝ᵥ u k) := by
    intro k σ
    have := hv k (σ.trans ρ)
    simp only [Equiv.trans_apply] at this
    simpa only [hrefl] using this
  have habs : |lam| ≤ lamStar := by
    rcases le_total 0 lam with h0 | h0
    · rw [abs_of_nonneg h0]
      exact hopt.2 (feas qh hanti a u v lam h0 hv)
    · rw [abs_of_nonpos h0]
      exact hopt.2 (feas qh hanti a u v (-lam) (by linarith) hvneg)
  have hl1 : lam ≤ lamStar := le_trans (le_abs_self lam) habs
  have hl2 : -lam ≤ lamStar := le_trans (neg_le_abs lam) habs
  unfold permutohull
  apply convexHull_min _ (convex_convexHull ℝ _)
  rintro _ ⟨σ, rfl⟩
  rcases eq_or_lt_of_le hzero with h0 | hpos
  · have hl : lam = lamStar := by linarith
    rw [hl]
    exact subset_convexHull ℝ _ ⟨σ, rfl⟩
  have hV : (∑ i, mix qh lamStar (σ i) • a i) ∈ convexHull ℝ
      (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, mix qh lamStar (σ i) • a i) :=
    subset_convexHull ℝ _ ⟨σ, rfl⟩
  have hV' : (∑ i, mix qh (-lamStar) (σ i) • a i) ∈ convexHull ℝ
      (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, mix qh lamStar (σ i) • a i) := by
    apply subset_convexHull ℝ _
    refine ⟨σ.trans ρ, ?_⟩
    simp only [Equiv.trans_apply, hrefl]
  set α := (lamStar + lam) / (2 * lamStar) with hα
  set β := (lamStar - lam) / (2 * lamStar) with hβ
  have hα0 : 0 ≤ α := div_nonneg (by linarith) (by linarith)
  have hβ0 : 0 ≤ β := div_nonneg (by linarith) (by linarith)
  have hαβ : α + β = 1 := by
    rw [hα, hβ, ← add_div]
    field_simp
    ring
  have hcomb : (∑ i, mix qh lam (σ i) • a i) =
      α • (∑ i, mix qh lamStar (σ i) • a i) + β • (∑ i, mix qh (-lamStar) (σ i) • a i) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    simp only [mix, hα, hβ]
    field_simp
    ring
  show (∑ i, mix qh lam (σ i) • a i) ∈ _
  rw [hcomb]
  exact (convex_convexHull ℝ _) hV hV' hα0 hβ0 hαβ
