-- Prove2me | solution 1 for TruncNewton.NegCurv.pd_of_cg_residual_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:56:26.660298+00:00
-- url     : https://prove2.me/submissions/0133a9fb-bf1e-47cb-84b9-fecb0002a1c2

import Mathlib
import Definitions.Def_TruncNewton_NegCurv_Setting



namespace TruncNewton.NegCurv

theorem tn_r_succ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    (cg H g (i+1)).r = (cg H g i).r - (inner ℝ (cg H g i).r (cg H g i).r /
      inner ℝ (cg H g i).d (H (cg H g i).d)) • H (cg H g i).d := rfl

theorem tn_d_succ {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    (cg H g (i+1)).d = (cg H g (i+1)).r + (inner ℝ (cg H g (i+1)).r (cg H g (i+1)).r /
      inner ℝ (cg H g i).r (cg H g i).r) • (cg H g i).d := rfl

theorem tn_r_zero {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : (cg H g 0).r = -g := rfl

theorem tn_d_zero {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) : (cg H g 0).d = -g := rfl

theorem tn_d_eq_zero_of_r_eq_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) (h : (cg H g i).r = 0) : (cg H g i).d = 0 := by
  cases i with
  | zero => rw [tn_d_zero]; rw [tn_r_zero] at h; exact h
  | succ i => rw [tn_d_succ, h]; simp

theorem tn_r_ne_zero {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ)
    (h : 0 < inner ℝ (cg H g i).d (H (cg H g i).d)) : (cg H g i).r ≠ 0 := by
  intro hr
  have := tn_d_eq_zero_of_r_eq_zero H g i hr
  rw [this] at h
  simp at h

theorem tn_inv_abs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (H : E →L[ℝ] E)
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (r d : ℕ → E) (a b : ℕ → ℝ) (k : ℕ)
    (hr : ∀ i, r (i+1) = r i - a i • H (d i))
    (hd0 : d 0 = r 0)
    (hd : ∀ i, d (i+1) = r (i+1) + b i • d i)
    (ha : ∀ i ≤ k, a i * inner ℝ (d i) (H (d i)) = inner ℝ (r i) (r i))
    (hb : ∀ i ≤ k, b i * inner ℝ (r i) (r i) = inner ℝ (r (i+1)) (r (i+1)))
    (hrne : ∀ i ≤ k, r i ≠ 0) :
    ∀ m ≤ k+1, (∀ j < m, inner ℝ (r m) (d j) = 0) ∧ (∀ j < m, inner ℝ (d m) (H (d j)) = 0) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ i ih =>
    intro hi
    have hik : i ≤ k := by omega
    obtain ⟨P1, P2⟩ := ih (by omega)
    have hrr : ∀ j ≤ k, inner ℝ (r j) (r j) ≠ 0 := fun j hj => by
      have := hrne j hj
      simpa using this
    have haj : ∀ j ≤ k, a j ≠ 0 := fun j hj h0 => by
      have := ha j hj
      rw [h0, zero_mul] at this
      exact hrr j hj this.symm
    -- F1
    have F1 : inner ℝ (r i) (d i) = inner ℝ (r i) (r i) := by
      cases i with
      | zero => rw [hd0]
      | succ i' =>
        rw [hd i', inner_add_right, real_inner_smul_right, P1 i' (Nat.lt_succ_self _)]
        ring
    -- F2
    have F2 : ∀ l ≤ i, inner ℝ (r (i+1)) (d l) = 0 := by
      intro l hl
      rw [hr i, inner_sub_left, real_inner_smul_left]
      rcases lt_or_eq_of_le hl with hl | hl
      · rw [P1 l hl, hs, P2 l hl]; ring
      · subst hl
        rw [F1, hs, ha l hik]; ring
    have F3 : ∀ l ≤ i, inner ℝ (r (i+1)) (r l) = 0 := by
      intro l hl
      cases l with
      | zero => rw [← hd0]; exact F2 0 hl
      | succ l' =>
        have : r (l'+1) = d (l'+1) - b l' • d l' := by rw [hd l']; abel
        rw [this, inner_sub_right, real_inner_smul_right, F2 _ hl, F2 l' (by omega)]; ring
    refine ⟨fun j hj => F2 j (by omega), ?_⟩
    intro j hj
    have hji : j ≤ i := by omega
    have hjk : j ≤ k := by omega
    have key : a j * inner ℝ (d (i+1)) (H (d j)) = 0 := by
      have e1 : a j • H (d j) = r j - r (j+1) := by rw [hr j]; abel
      have e2 : a j * inner ℝ (r (i+1)) (H (d j)) = inner ℝ (r (i+1)) (r j) - inner ℝ (r (i+1)) (r (j+1)) := by
        rw [← real_inner_smul_right, e1, inner_sub_right]
      rw [hd i, inner_add_left, real_inner_smul_left, mul_add]
      have e3 : a j * (b i * inner ℝ (d i) (H (d j))) = b i * (a j * inner ℝ (d i) (H (d j))) := by ring
      rw [e2, e3]
      rcases lt_or_eq_of_le hji with hj' | hj'
      · rw [P2 j hj', F3 j hji, F3 (j+1) (by omega)]; ring
      · subst hj'
        rw [F3 j le_rfl, ha j hik, ← hb j hik]
        ring
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h (haj j hjk)
    · exact h

theorem tn_sa {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (H x) y = inner ℝ x (H y) := by
  have := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH) x y
  simpa using this

theorem tn_cg_inv {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hc : ∀ i ≤ k, 0 < inner ℝ (cg H g i).d (H (cg H g i).d)) :
    ∀ m ≤ k+1, (∀ j < m, inner ℝ (cg H g m).r (cg H g j).d = 0) ∧
      (∀ j < m, inner ℝ (cg H g m).d (H (cg H g j).d) = 0) := by
  refine tn_inv_abs H hs (fun i => (cg H g i).r) (fun i => (cg H g i).d)
    (fun i => inner ℝ (cg H g i).r (cg H g i).r / inner ℝ (cg H g i).d (H (cg H g i).d))
    (fun i => inner ℝ (cg H g (i+1)).r (cg H g (i+1)).r / inner ℝ (cg H g i).r (cg H g i).r)
    k ?_ ?_ ?_ ?_ ?_ ?_
  · intro i; exact tn_r_succ H g i
  · rfl
  · intro i; exact tn_d_succ H g i
  · intro i hi
    exact div_mul_cancel₀ _ (hc i hi).ne'
  · intro i hi
    have h := tn_r_ne_zero H g i (hc i hi)
    have : inner ℝ (cg H g i).r (cg H g i).r ≠ 0 := by simpa using h
    exact div_mul_cancel₀ _ this
  · intro i hi; exact tn_r_ne_zero H g i (hc i hi)

theorem tn_D_props {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hc : ∀ i ≤ k, 0 < inner ℝ (cg H g i).d (H (cg H g i).d))
    (hrk : (cg H g (k+1)).r = 0) :
    (∀ w ∈ Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iio (k+1)),
      H w ∈ Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iio (k+1))) ∧
    g ∈ Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iio (k+1)) := by
  set D := Submodule.span ℝ ((fun i => (cg H g i).d) '' Set.Iio (k+1)) with hD
  have hdD : ∀ j ≤ k, (cg H g j).d ∈ D := fun j hj =>
    Submodule.subset_span ⟨j, by simpa [Nat.lt_succ_iff] using hj, rfl⟩
  have hrD : ∀ j ≤ k, (cg H g j).r ∈ D := by
    intro j hj
    cases j with
    | zero => rw [tn_r_zero]; have := hdD 0 hj; rwa [tn_d_zero] at this
    | succ l =>
      have : (cg H g (l+1)).r = (cg H g (l+1)).d - (inner ℝ (cg H g (l+1)).r (cg H g (l+1)).r /
        inner ℝ (cg H g l).r (cg H g l).r) • (cg H g l).d := by rw [tn_d_succ]; abel
      rw [this]
      exact D.sub_mem (hdD _ hj) (D.smul_mem _ (hdD l (by omega)))
  have hHd : ∀ j ≤ k, H (cg H g j).d ∈ D := by
    intro j hj
    have hne : inner ℝ (cg H g j).r (cg H g j).r / inner ℝ (cg H g j).d (H (cg H g j).d) ≠ 0 := by
      apply div_ne_zero
      · have h := tn_r_ne_zero H g j (hc j hj)
        simpa using h
      · exact (hc j hj).ne'
    set a := inner ℝ (cg H g j).r (cg H g j).r / inner ℝ (cg H g j).d (H (cg H g j).d) with ha
    have e : H (cg H g j).d = a⁻¹ • ((cg H g j).r - (cg H g (j+1)).r) := by
      rw [tn_r_succ H g j, ← ha]
      rw [sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [e]
    refine D.smul_mem _ (D.sub_mem (hrD j hj) ?_)
    by_cases hjk : j + 1 ≤ k
    · exact hrD _ hjk
    · have : j = k := by omega
      subst this; rw [hrk]; exact D.zero_mem
  refine ⟨?_, ?_⟩
  · intro w hw
    have : D ≤ D.comap (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) := by
      rw [hD, Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hHd j (by simpa [Nat.lt_succ_iff] using hj)
    exact this hw
  · have := hdD 0 (Nat.zero_le _)
    rw [tn_d_zero] at this
    simpa using D.neg_mem this

theorem tn_pd_span {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (d : ℕ → EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hconj : ∀ i j, i < N → j < N → i ≠ j → inner ℝ (d i) (H (d j)) = 0)
    (hpos : ∀ i, i < N → 0 < inner ℝ (d i) (H (d i))) :
    ∀ w ∈ Submodule.span ℝ (d '' Set.Iio N), w ≠ 0 → 0 < inner ℝ w (H w) := by
  have key : ∀ w ∈ Submodule.span ℝ (d '' Set.Iio N),
      ∃ c : ℕ → ℝ, w = ∑ i ∈ Finset.range N, c i • d i := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      refine ⟨fun i => if i = j then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · intro hj'; exact absurd (Finset.mem_range.mpr hj) hj'
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c1, rfl⟩ := hx
      obtain ⟨c2, rfl⟩ := hy
      exact ⟨fun i => c1 i + c2 i, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul a x _ hx =>
      obtain ⟨c1, rfl⟩ := hx
      exact ⟨fun i => a * c1 i, by simp [Finset.smul_sum, smul_smul]⟩
  intro w hw hne
  obtain ⟨c, rfl⟩ := key w hw
  have hform : inner ℝ (∑ i ∈ Finset.range N, c i • d i) (H (∑ i ∈ Finset.range N, c i • d i))
      = ∑ i ∈ Finset.range N, c i ^ 2 * inner ℝ (d i) (H (d i)) := by
    rw [map_sum]
    simp only [map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · ring
    · intro j hj hji
      rw [hconj j i (Finset.mem_range.mp hj) (Finset.mem_range.mp hi) hji]; ring
    · intro h; exact absurd hi h
  rw [hform]
  have : ∃ i ∈ Finset.range N, c i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    exact Finset.sum_eq_zero (fun i hi => by rw [hcon i hi, zero_smul])
  obtain ⟨i, hi, hci⟩ := this
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (sq_nonneg _) (hpos j (Finset.mem_range.mp hj)).le
  · exact ⟨i, hi, mul_pos (by positivity) (hpos i (Finset.mem_range.mp hi))⟩

theorem tn_eig_pos {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hs : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hinv : ∀ w ∈ K, H w ∈ K) (hpd : ∀ w ∈ K, w ≠ 0 → 0 < inner ℝ w (H w))
    (g : EuclideanSpace ℝ (Fin n)) (hg : g ∈ K) (μ : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) (hv : H v = μ • v) (hgv : inner ℝ g v ≠ 0) : 0 < μ := by
  set vK := K.starProjection v with hvK
  have hmem : vK ∈ K := Submodule.starProjection_apply_mem K v
  have horth : ∀ u ∈ K, inner ℝ (v - vK) u = 0 := fun u hu =>
    Submodule.starProjection_inner_eq_zero v u hu
  have heig : H vK = μ • vK := by
    obtain ⟨u, hu⟩ : ∃ u, u = H vK - μ • vK := ⟨_, rfl⟩
    have h1 : u ∈ K := by rw [hu]; exact K.sub_mem (hinv _ hmem) (K.smul_mem _ hmem)
    have a1 := horth (H u) (hinv u h1)
    have a2 := horth u h1
    rw [inner_sub_left] at a1 a2
    have f3 : inner ℝ v (H u) = μ * inner ℝ v u := by
      rw [← hs, hv, real_inner_smul_left]
    have h2 : inner ℝ u u = 0 := by
      have : inner ℝ u u = inner ℝ (H vK - μ • vK) u := by rw [← hu]
      rw [this, inner_sub_left, real_inner_smul_left, hs]
      have f1 : inner ℝ vK (H u) = inner ℝ v (H u) := by linarith
      have f2 : inner ℝ vK u = inner ℝ v u := by linarith
      rw [f1, f2, f3]; ring
    have : u = 0 := inner_self_eq_zero.mp h2
    rw [this] at hu
    exact (sub_eq_zero.mp hu.symm)
  have hgv' : inner ℝ g vK ≠ 0 := by
    have := horth g hg
    rw [real_inner_comm, inner_sub_right] at this
    intro h
    apply hgv
    rw [h] at this
    linarith
  have hne : vK ≠ 0 := by
    intro h; apply hgv'; rw [h]; simp
  have hp := hpd vK hmem hne
  rw [heig, real_inner_smul_right] at hp
  have hpos : 0 < inner ℝ vK vK := real_inner_self_pos.mpr hne
  by_contra hμ
  push_neg at hμ
  nlinarith

theorem tn_pd_of_eig {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H)
    (hpos : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → 0 < μ) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by
  have hT : (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hH
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  set b := hT.eigenvectorBasis hn with hbdef
  intro v hv
  have hb : ∀ i, H (b i) = hT.eigenvalues hn i • b i := fun i => hT.apply_eigenvectorBasis hn i
  have hlam : ∀ i, 0 < hT.eigenvalues hn i := fun i =>
    hpos _ ⟨b i, b.orthonormal.ne_zero i, hb i⟩
  have hsum : inner ℝ v (H v) = ∑ i, hT.eigenvalues hn i * (inner ℝ (b i) v)^2 := by
    rw [← b.sum_inner_mul_inner v (H v)]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : inner ℝ (b i) (H v) = hT.eigenvalues hn i * inner ℝ (b i) v := by
      rw [← tn_sa H hH, hb, real_inner_smul_left]
    rw [h1, real_inner_comm (b i) v]
    ring
  rw [hsum]
  have : ∃ i, inner ℝ (b i) v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv
    rw [← b.sum_repr' v]
    exact Finset.sum_eq_zero (fun i _ => by rw [hcon i, zero_smul])
  obtain ⟨i, hi⟩ := this
  apply Finset.sum_pos'
  · intro j _; exact mul_nonneg (hlam j).le (sq_nonneg _)
  · exact ⟨i, Finset.mem_univ _, mul_pos (hlam i) (by positivity)⟩

theorem tn_r_orth {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ)
    (h : ∀ j < m, inner ℝ (cg H g m).r (cg H g j).d = 0) :
    ∀ j < m, inner ℝ (cg H g m).r (cg H g j).r = 0 := by
  intro j hj
  cases j with
  | zero => rw [tn_r_zero]; have := h 0 hj; rwa [tn_d_zero] at this
  | succ l =>
    have e : (cg H g (l+1)).r = (cg H g (l+1)).d - (inner ℝ (cg H g (l+1)).r (cg H g (l+1)).r /
        inner ℝ (cg H g l).r (cg H g l).r) • (cg H g l).d := by rw [tn_d_succ]; abel
    rw [e, inner_sub_right, real_inner_smul_right, h _ hj, h l (by omega)]; ring

theorem tn_pd_core {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (i : ℕ) (hcurv : ∀ j ≤ i, 0 < inner ℝ ((cg H g j).d) (H (cg H g j).d))
    (hr : (cg H g (i + 1)).r = 0) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by
  have hs := tn_sa H hH
  obtain ⟨hinv, hgD⟩ := tn_D_props H g i hcurv hr
  have hI := tn_cg_inv H hs g i hcurv
  have hpd := tn_pd_span H (fun j => (cg H g j).d) (i+1) (by
    intro a c ha hc hac
    rcases lt_or_gt_of_ne hac with h | h
    · rw [← hs, real_inner_comm]; exact (hI c (by omega)).2 a h
    · exact (hI a (by omega)).2 c h) (fun j hj => hcurv j (by omega))
  apply tn_pd_of_eig H hH
  rintro μ ⟨v, hv0, hv⟩
  obtain ⟨v', hv', hgv'⟩ := hg μ ⟨v, hv0, hv⟩
  exact tn_eig_pos H hs _ hinv hpd g hgD μ v' hv' hgv'

theorem tn_goal_core {n : ℕ} (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hnpd : ¬ ∀ v, v ≠ 0 → 0 < inner ℝ v (H v)) :
    (∃ i, ExitsVia21 H g 0 0 i) ∨
      (∀ μ : ℝ, μ ≤ 0 → ∀ v, H v = μ • v → inner ℝ g v = 0) := by
  have hs := tn_sa H hH
  by_cases hex : ∃ i, ExitsVia21 H g 0 0 i
  · exact Or.inl hex
  right
  push_neg at hex
  have hstop : ∃ i, ¬ (0 < inner ℝ (cg H g i).d (H (cg H g i).d)) ∨ (cg H g (i+1)).r = 0 := by
    by_contra hcon
    push_neg at hcon
    have hc : ∀ i ≤ n, 0 < inner ℝ (cg H g i).d (H (cg H g i).d) := fun i _ => (hcon i).1
    have hI := tn_cg_inv H hs g n hc
    have hne : ∀ j : Fin (n+1), (cg H g j).r ≠ 0 := by
      intro ⟨j, hj⟩
      cases j with
      | zero => exact tn_r_ne_zero H g 0 (hc 0 (Nat.zero_le _))
      | succ l => exact (hcon l).2
    have hli : LinearIndependent ℝ (fun j : Fin (n+1) => (cg H g j).r) := by
      apply linearIndependent_of_ne_zero_of_inner_eq_zero hne
      intro a c hac
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hac) with h | h
      · rw [real_inner_comm]
        exact tn_r_orth H g c ((hI c (by omega)).1) a h
      · exact tn_r_orth H g a ((hI a (by omega)).1) c h
    have := hli.fintype_card_le_finrank
    simp at this
  classical
  have hmin := fun j (hj : j < Nat.find hstop) => Nat.find_min hstop hj
  have hPi := Nat.find_spec hstop
  set i := Nat.find hstop with hi
  by_cases hc : 0 < inner ℝ (cg H g i).d (H (cg H g i).d)
  · have hr : (cg H g (i+1)).r = 0 := by
      rcases hPi with h | h
      · exact absurd hc h
      · exact h
    have hcurv : ∀ j ≤ i, 0 < inner ℝ (cg H g j).d (H (cg H g j).d) := by
      intro j hj
      rcases lt_or_eq_of_le hj with h | h
      · have := hmin j h
        push_neg at this
        exact this.1
      · rw [h]; exact hc
    obtain ⟨hinv, hgD⟩ := tn_D_props H g i hcurv hr
    have hI := tn_cg_inv H hs g i hcurv
    have hpd := tn_pd_span H (fun j => (cg H g j).d) (i+1) (by
      intro a c ha hc hac
      rcases lt_or_gt_of_ne hac with h | h
      · rw [← hs, real_inner_comm]; exact (hI c (by omega)).2 a h
      · exact (hI a (by omega)).2 c h) (fun j hj => hcurv j (by omega))
    intro μ hμ v hv
    by_contra hgv
    have := tn_eig_pos H hs _ hinv hpd g hgD μ v hv hgv
    linarith
  · exfalso
    apply hex i
    refine ⟨?_, ?_⟩
    · intro j hj
      have := hmin j hj
      push_neg at this
      refine ⟨?_, ?_⟩
      · simp only [test21]; push_neg; simpa using this.1
      · simp only [test22]; push_neg; simpa using this.2
    · simp only [test21]; push_neg at hc; simpa using hc

end TruncNewton.NegCurv

open TruncNewton.NegCurv


theorem solution {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (g : EuclideanSpace ℝ (Fin n))
    (hg : ∀ μ : ℝ, (∃ v, v ≠ 0 ∧ H v = μ • v) → ∃ v, H v = μ • v ∧ inner ℝ g v ≠ 0)
    (i : ℕ) (hcurv : ∀ j ≤ i, 0 < inner ℝ ((cg H g j).d) (H (cg H g j).d))
    (hr : (cg H g (i + 1)).r = 0) :
    ∀ v, v ≠ 0 → 0 < inner ℝ v (H v) := by
  exact tn_pd_core H hH g hg i hcurv hr
