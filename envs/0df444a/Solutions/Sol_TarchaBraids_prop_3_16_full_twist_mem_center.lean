-- Prove2me | solution 1 for TarchaBraids.prop_3_16_full_twist_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-19T05:27:01.746081+00:00
-- url     : https://prove2.me/submissions/b746f22d-5c7b-4d18-8d80-d7331cde0f35

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

open BraidsLinksMCG

/-! ### Pure group-theoretic steps -/

private lemma ftw_shift_base {G : Type*} [Group G] {x r s : G}
    (hc : Commute x s) (hb : r * s * r = s * r * s) :
    (x * r * s) * r = s * (x * r * s) := by
  calc (x * r * s) * r = x * (r * s * r) := by group
    _ = x * (s * r * s) := by rw [hb]
    _ = (x * s) * (r * s) := by group
    _ = (s * x) * (r * s) := by rw [hc.eq]
    _ = s * (x * r * s) := by group

private lemma ftw_shift_step {G : Type*} [Group G] {X g r s : G}
    (hX : X * r = s * X) (hc : Commute r g) :
    (X * g) * r = s * (X * g) := by
  calc (X * g) * r = X * (g * r) := by group
    _ = X * (r * g) := by rw [hc.eq]
    _ = (X * r) * g := by group
    _ = (s * X) * g := by rw [hX]
    _ = s * (X * g) := by group

private lemma ftw_wrap_step {G : Type*} [Group G] {D r s g0 : G}
    (hIH : D * D * r = g0 * (D * D))
    (hsD : s * D = D * (r⁻¹ * s * r))
    (hb : s * r * s = r * s * r) :
    (D * s) * (D * s) * s = g0 * ((D * s) * (D * s)) := by
  have hg0 : g0 = D * D * r * (D * D)⁻¹ := eq_mul_inv_of_mul_eq hIH.symm
  have hL : (D * s) * (D * s) * s = D * D * (r⁻¹ * (s * r * s) * s) := by
    calc (D * s) * (D * s) * s = D * (s * D) * s * s := by group
      _ = D * (D * (r⁻¹ * s * r)) * s * s := by rw [hsD]
      _ = D * D * (r⁻¹ * (s * r * s) * s) := by group
  have hR : g0 * ((D * s) * (D * s)) = D * D * (r⁻¹ * (s * r * s) * s) := by
    calc g0 * ((D * s) * (D * s))
        = D * D * r * (D * D)⁻¹ * (D * (s * D) * s) := by rw [hg0]; group
      _ = D * D * r * (D * D)⁻¹ * (D * (D * (r⁻¹ * s * r)) * s) := by rw [hsD]
      _ = D * D * (s * r * s) := by group
      _ = D * D * (r⁻¹ * (r * s * r) * s) := by group
      _ = D * D * (r⁻¹ * (s * r * s) * s) := by rw [hb]
  rw [hL, hR]

private lemma ftw_conj_step {G : Type*} [Group G] {T a d : G}
    (hTa : T * a = a * T) (hTd : Commute T d) :
    T * (d * a * d⁻¹) = (d * a * d⁻¹) * T := by
  calc T * (d * a * d⁻¹) = (T * d) * a * d⁻¹ := by group
    _ = d * (T * a) * d⁻¹ := by rw [hTd.eq]; group
    _ = d * (a * T) * d⁻¹ := by rw [hTa]
    _ = d * a * (T * d⁻¹) := by group
    _ = d * a * (d⁻¹ * T) := by rw [hTd.inv_right.eq]
    _ = (d * a * d⁻¹) * T := by group

/-! ### The defining relations, read off from the presentation -/

private lemma ftw_comm_rel {n : ℕ} {i j : Fin (n - 1)}
    (h : 2 ≤ ((i : ℤ) - (j : ℤ)).natAbs) :
    sigma i * sigma j = sigma j * sigma i := by
  have hr : (FreeGroup.of i * FreeGroup.of j * (FreeGroup.of i)⁻¹ * (FreeGroup.of j)⁻¹)
      ∈ braidRels n := Or.inl ⟨i, j, h, rfl⟩
  have h1 := PresentedGroup.one_of_mem hr
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : sigma i * sigma j * (sigma i)⁻¹ * (sigma j)⁻¹ = 1 := h1
  have h3 : (sigma i * sigma j) * (sigma j * sigma i)⁻¹ = 1 := by
    rw [mul_inv_rev]
    simpa [mul_assoc] using h2
  exact mul_inv_eq_one.mp h3

private lemma ftw_braid_rel {n : ℕ} {i j : Fin (n - 1)} (h : (j : ℕ) = (i : ℕ) + 1) :
    sigma i * sigma j * sigma i = sigma j * sigma i * sigma j := by
  have hr : (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i *
      (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∈ braidRels n :=
    Or.inr ⟨i, j, h, rfl⟩
  have h1 := PresentedGroup.one_of_mem hr
  rw [map_mul, map_mul, map_mul, map_inv, map_mul, map_mul] at h1
  have h2 : sigma i * sigma j * sigma i * (sigma j * sigma i * sigma j)⁻¹ = 1 := h1
  exact mul_inv_eq_one.mp h2

/-! ### Generators indexed by `ℕ`, and their partial products -/

/-- `gg n k` is the `k`-th Artin generator of `B_n` when `k` is in range, and `1` otherwise. -/
private def gg (n k : ℕ) : ArtinBraidGroup n :=
  if h : k < n - 1 then sigma ⟨k, h⟩ else 1

/-- `dd n k` is the product `σ₁ σ₂ ⋯ σ_k` of the first `k` generators. -/
private def dd (n k : ℕ) : ArtinBraidGroup n := ((List.range k).map (gg n)).prod

private lemma dd_zero (n : ℕ) : dd n 0 = 1 := rfl

private lemma dd_succ (n k : ℕ) : dd n (k + 1) = dd n k * gg n k := by
  simp [dd, List.range_succ]

private lemma gg_commute {n j k : ℕ} (h : j + 2 ≤ k) : Commute (gg n j) (gg n k) := by
  by_cases hj : j < n - 1
  · by_cases hk : k < n - 1
    · have hd : (2 : ℕ) ≤ (((⟨j, hj⟩ : Fin (n - 1)) : ℤ)
          - ((⟨k, hk⟩ : Fin (n - 1)) : ℤ)).natAbs := by
        simp only [Fin.val_mk]
        omega
      simpa [gg, hj, hk, Commute, SemiconjBy] using ftw_comm_rel (n := n) hd
    · simp [gg, hk]
  · simp [gg, hj]

private lemma gg_braid {n k : ℕ} (h : k + 1 < n - 1) :
    gg n k * gg n (k + 1) * gg n k = gg n (k + 1) * gg n k * gg n (k + 1) := by
  have hk : k < n - 1 := by omega
  have := ftw_braid_rel (n := n) (i := ⟨k, hk⟩) (j := ⟨k + 1, h⟩) rfl
  simpa [gg, hk, h] using this

private lemma dd_commute_gg {n k i : ℕ} (h : k + 1 ≤ i) : Commute (dd n k) (gg n i) := by
  refine Commute.list_prod_left _ _ ?_
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
  exact gg_commute (by simp only [List.mem_range] at hj; omega)

/-! ### The shift relation -/

private lemma dd_shift {n i : ℕ} (hi : i + 1 < n - 1) :
    ∀ K, i + 2 ≤ K → dd n K * gg n i = gg n (i + 1) * dd n K := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base =>
      have h1 : dd n (i + 2) = dd n i * gg n i * gg n (i + 1) := by
        rw [show i + 2 = (i + 1) + 1 from rfl, dd_succ, dd_succ]
      have hc : Commute (dd n i) (gg n (i + 1)) := dd_commute_gg (by omega)
      rw [h1]
      exact ftw_shift_base hc (gg_braid hi)
  | succ K hK ih =>
      have hc : Commute (gg n i) (gg n K) := gg_commute (by omega)
      rw [dd_succ]
      exact ftw_shift_step ih hc

/-! ### The wrap-around relation -/

private lemma dd_sq_wrap {n : ℕ} :
    ∀ k, k + 1 ≤ n - 1 →
      dd n (k + 1) * dd n (k + 1) * gg n k = gg n 0 * (dd n (k + 1) * dd n (k + 1)) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [dd_succ, dd_zero, one_mul]
      group
  | succ k ih =>
      intro hk
      have hIH := ih (by omega)
      have hDdef : dd n (k + 1) = dd n k * gg n k := dd_succ n k
      have hc : Commute (dd n k) (gg n (k + 1)) := dd_commute_gg (by omega)
      have hsD : gg n (k + 1) * dd n (k + 1)
          = dd n (k + 1) * ((gg n k)⁻¹ * gg n (k + 1) * gg n k) := by
        calc gg n (k + 1) * dd n (k + 1)
            = (gg n (k + 1) * dd n k) * gg n k := by rw [hDdef]; group
          _ = (dd n k * gg n (k + 1)) * gg n k := by rw [hc.eq]
          _ = (dd n k * gg n k) * ((gg n k)⁻¹ * gg n (k + 1) * gg n k) := by group
          _ = dd n (k + 1) * ((gg n k)⁻¹ * gg n (k + 1) * gg n k) := by rw [hDdef]
      have hb : gg n (k + 1) * gg n k * gg n (k + 1)
          = gg n k * gg n (k + 1) * gg n k := (gg_braid (n := n) (k := k) (by omega)).symm
      rw [dd_succ n (k + 1)]
      exact ftw_wrap_step hIH hsD hb

/-! ### `sigmaProd` as a partial product -/

private lemma ofFn_prod_eq_range_prod {G : Type} [Group G] (M : ℕ) (f : Fin M → G) :
    (List.ofFn f).prod
      = ((List.range M).map (fun k => if h : k < M then f ⟨k, h⟩ else 1)).prod := by
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    have hi : i < M := by simpa using h1
    simp [hi]

private lemma sigmaProd_eq_dd (n : ℕ) : sigmaProd n = dd n (n - 1) := by
  rw [sigmaProd, dd, ofFn_prod_eq_range_prod]
  rfl

/-! ### The full twist is central -/

theorem solution (n : ℕ) :
    sigmaProd n ^ n ∈ Subgroup.center (ArtinBraidGroup n) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have h0 : n - 1 = 0 := by omega
    have h1 : sigmaProd n = 1 := by rw [sigmaProd_eq_dd, h0, dd_zero]
    rw [h1, one_pow]
    exact Subgroup.one_mem _
  · have hδd : sigmaProd n = dd n (n - 1) := sigmaProd_eq_dd n
    have hshift : ∀ i, i + 1 < n - 1 →
        sigmaProd n * gg n i = gg n (i + 1) * sigmaProd n := by
      intro i hi
      rw [hδd]
      exact dd_shift hi (n - 1) (by omega)
    have hiter : ∀ k, k < n - 1 →
        sigmaProd n ^ k * gg n 0 = gg n k * sigmaProd n ^ k := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
          intro hk
          have h1 := ih (by omega)
          calc sigmaProd n ^ (k + 1) * gg n 0
              = sigmaProd n * (sigmaProd n ^ k * gg n 0) := by rw [pow_succ']; group
            _ = sigmaProd n * (gg n k * sigmaProd n ^ k) := by rw [h1]
            _ = (sigmaProd n * gg n k) * sigmaProd n ^ k := by group
            _ = (gg n (k + 1) * sigmaProd n) * sigmaProd n ^ k := by rw [hshift k hk]
            _ = gg n (k + 1) * sigmaProd n ^ (k + 1) := by rw [pow_succ']; group
    have hwrap : sigmaProd n ^ 2 * gg n (n - 2) = gg n 0 * sigmaProd n ^ 2 := by
      have h := dd_sq_wrap (n := n) (n - 2) (by omega)
      rw [show n - 2 + 1 = n - 1 by omega] at h
      rw [hδd, pow_two]
      exact h
    have hsplit : sigmaProd n ^ n = sigmaProd n ^ 2 * sigmaProd n ^ (n - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hzero : sigmaProd n ^ n * gg n 0 = gg n 0 * sigmaProd n ^ n := by
      have h1 := hiter (n - 2) (by omega)
      calc sigmaProd n ^ n * gg n 0
          = sigmaProd n ^ 2 * (sigmaProd n ^ (n - 2) * gg n 0) := by rw [hsplit]; group
        _ = sigmaProd n ^ 2 * (gg n (n - 2) * sigmaProd n ^ (n - 2)) := by rw [h1]
        _ = (sigmaProd n ^ 2 * gg n (n - 2)) * sigmaProd n ^ (n - 2) := by group
        _ = (gg n 0 * sigmaProd n ^ 2) * sigmaProd n ^ (n - 2) := by rw [hwrap]
        _ = gg n 0 * sigmaProd n ^ n := by rw [hsplit]; group
    have hall : ∀ i, i < n - 1 →
        sigmaProd n ^ n * gg n i = gg n i * sigmaProd n ^ n := by
      intro i
      induction i with
      | zero => intro _; exact hzero
      | succ i ih =>
          intro hi
          have h1 := ih (by omega)
          have h2 := hshift i (by omega)
          have hginv : gg n (i + 1) = sigmaProd n * gg n i * (sigmaProd n)⁻¹ :=
            eq_mul_inv_of_mul_eq h2.symm
          have hTd : Commute (sigmaProd n ^ n) (sigmaProd n) :=
            (Commute.refl (sigmaProd n)).pow_left n
          rw [hginv]
          exact ftw_conj_step h1 hTd
    rw [Subgroup.mem_center_iff]
    intro y
    have hgenmem : ∀ j : Fin (n - 1),
        sigma j ∈ Subgroup.centralizer ({sigmaProd n ^ n} : Set (ArtinBraidGroup n)) := by
      intro j
      rw [Subgroup.mem_centralizer_iff]
      rintro h (rfl : h = sigmaProd n ^ n)
      have hj : (j : ℕ) < n - 1 := j.isLt
      have h3 := hall (j : ℕ) hj
      simpa [gg, hj] using h3
    have hmem : y ∈ Subgroup.centralizer ({sigmaProd n ^ n} : Set (ArtinBraidGroup n)) :=
      PresentedGroup.generated_by (braidRels n) _ hgenmem y
    exact ((Subgroup.mem_centralizer_iff.mp hmem) (sigmaProd n ^ n) rfl).symm
