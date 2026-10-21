-- Prove2me | solution 1 for ShapeMoment.LogConcave.tight_count
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:06:40.237986+00:00
-- url     : https://prove2.me/submissions/d1e23be3-4b02-426d-80e9-2ae302095063

import Mathlib
import Definitions.Def_ShapeMoment_LogConcave_Model

set_option autoImplicit false
open ShapeMoment.LogConcave

lemma sm_ext_val {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ext x (j.val + 1) = x j := by
  unfold ext
  rw [dif_pos ⟨by omega, by omega⟩]
  simp

lemma sm_ext_out {n : ℕ} (x : Fin n → ℝ) (i : ℕ) (h : ¬ (1 ≤ i ∧ i ≤ n)) : ext x i = 0 := by
  unfold ext
  rw [dif_neg h]

lemma sm_ext_zero_of_out {n : ℕ} (x : Fin n → ℝ) (k ℓ : ℕ) (hk : 1 ≤ k) (hle : ℓ ≤ n)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) (i : ℕ)
    (hi : ¬ (k ≤ i ∧ i ≤ ℓ)) : ext x i = 0 := by
  by_cases h : 1 ≤ i ∧ i ≤ n
  · have := hzero ⟨i - 1, by omega⟩ (by simp only; omega)
    unfold ext
    rw [dif_pos h]; exact this
  · exact sm_ext_out x i h


lemma sm_ext_add {n : ℕ} (x y : Fin n → ℝ) (i : ℕ) : ext (x + y) i = ext x i + ext y i := by
  unfold ext
  split_ifs <;> simp

lemma sm_ext_smul {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (i : ℕ) : ext (s • x) i = s * ext x i := by
  unfold ext
  split_ifs <;> simp

lemma sm_moment_add {n : ℕ} (x y : Fin n → ℝ) (i : ℕ) :
    moment (x + y) i = moment x i + moment y i := by
  simp [moment, mul_add, Finset.sum_add_distrib]

lemma sm_moment_smul {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (i : ℕ) :
    moment (s • x) i = s * moment x i := by
  simp [moment, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma sm_Q_le (a b c p q r : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a * c = b ^ 2)
    (hlin : c * p + a * r = 2 * b * q) : p * r ≤ q ^ 2 := by
  have h1 : (c * p) * (a * r) ≤ ((c * p + a * r) / 2) ^ 2 := by
    nlinarith [sq_nonneg (c * p - a * r)]
  have h2 : (c * p + a * r) / 2 = b * q := by linarith
  rw [h2] at h1
  have h3 : b ^ 2 * (p * r) ≤ b ^ 2 * q ^ 2 := by
    calc b ^ 2 * (p * r) = (c * p) * (a * r) := by rw [← hac]; ring
      _ ≤ (b * q) ^ 2 := h1
      _ = b ^ 2 * q ^ 2 := by ring
  exact le_of_mul_le_mul_left h3 (by positivity)

lemma sm_ev_pos (A B : ℝ) (hA : 0 < A) : ∀ᶠ s in nhds (0 : ℝ), 0 < A + s * B := by
  have hc : ContinuousAt (fun s : ℝ => A + s * B) 0 := by fun_prop
  have := ContinuousAt.eventually_lt (continuousAt_const (y := (0:ℝ)) (x := (0:ℝ))) hc (by simpa using hA)
  exact this

lemma sm_ev_lt (a b c p q r : ℝ) (h : a * c < b ^ 2) :
    ∀ᶠ s in nhds (0 : ℝ), (a + s * p) * (c + s * r) ≤ (b + s * q) ^ 2 := by
  have hf : ContinuousAt (fun s : ℝ => (a + s * p) * (c + s * r)) 0 := by fun_prop
  have hg : ContinuousAt (fun s : ℝ => (b + s * q) ^ 2) 0 := by fun_prop
  have := ContinuousAt.eventually_lt hf hg (by simpa using h)
  exact this.mono (fun s hs => hs.le)

lemma sm_perturb (n m : ℕ) (q : ℕ → ℝ) (x d : Fin n → ℝ) (k ℓ : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ)
    (hle : ℓ ≤ n) (hmom : ∀ i ≤ m, moment x i = q i)
    (hlc : ∀ j, k < j → j < ℓ → ext x (j - 1) * ext x (j + 1) ≤ ext x j ^ 2)
    (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0)
    (hdmom : ∀ i ≤ m, moment d i = 0)
    (hdz : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → d j = 0)
    (hdt : ∀ j, k < j → j < ℓ → ext x (j - 1) * ext x (j + 1) = ext x j ^ 2 →
      ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1) = 2 * ext x j * ext d j) :
    ∀ᶠ s in nhds (0 : ℝ), x + s • d ∈ feasLC n m q := by
  have h1 : ∀ᶠ s in nhds (0 : ℝ), ∀ j ∈ Finset.Icc k ℓ, 0 < ext x j + s * ext d j := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact sm_ev_pos _ _ (hpos j hj.1 hj.2)
  have h2 : ∀ᶠ s in nhds (0 : ℝ), ∀ j ∈ Finset.Ioo k ℓ,
      (ext x (j - 1) + s * ext d (j - 1)) * (ext x (j + 1) + s * ext d (j + 1)) ≤
        (ext x j + s * ext d j) ^ 2 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    rw [Finset.mem_Ioo] at hj
    rcases (hlc j hj.1 hj.2).lt_or_eq with hlt | heq
    · exact sm_ev_lt _ _ _ _ _ _ hlt
    · refine Filter.Eventually.of_forall (fun s => ?_)
      have hlin := hdt j hj.1 hj.2 heq
      have hQ := sm_Q_le (ext x (j - 1)) (ext x j) (ext x (j + 1)) (ext d (j - 1)) (ext d j)
        (ext d (j + 1)) (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))
        (hpos _ (by omega) (by omega)) heq (by linarith)
      have e : s * (ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1)) =
          s * (2 * ext x j * ext d j) := by rw [hlin]
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hQ), e, heq]
  filter_upwards [h1, h2] with s hs1 hs2
  refine ⟨k, ℓ, hk, hkl, hle, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [sm_moment_add, sm_moment_smul, hdmom i hi, hmom i hi]; ring
  · intro j hj1 hj2
    have := hs2 j (Finset.mem_Ioo.2 ⟨hj1, hj2⟩)
    simpa only [sm_ext_add, sm_ext_smul] using this
  · intro j hj1 hj2
    have := hs1 j (Finset.mem_Icc.2 ⟨hj1, hj2⟩)
    simpa only [sm_ext_add, sm_ext_smul] using this
  · intro j hj
    simp [hzero j hj, hdz j hj]

abbrev SmO (n k ℓ : ℕ) := {j : Fin n // ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ)}

theorem solution (n m : ℕ) (q : ℕ → ℝ) (f : Fin n → ℝ)
    (hq0 : q 0 = 1) (x : Fin n → ℝ)
    (hext : x ∈ (feasLC n m q).extremePoints ℝ)
    (hopt : IsMaxSol f (feasLC n m q) x)
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkle : k ≤ ℓ) (hle : ℓ ≤ n)
    (hpos : ∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j)
    (hzero : ∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0) :
    (ℓ - k + 1) - (m + 1) ≤
      ((Finset.Ioo k ℓ).filter
        (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  set T := (Finset.Ioo k ℓ).filter (fun j => ext x (j - 1) * ext x (j + 1) = ext x j ^ 2) with hT
  obtain ⟨hxF, hextr⟩ := mem_extremePoints.1 hext
  obtain ⟨k', ℓ', hk', hkl', hle', hmom, hlc', hpos', hzero'⟩ := hxF
  have hz := sm_ext_zero_of_out x k ℓ hk hle hzero
  have hz' := sm_ext_zero_of_out x k' ℓ' hk' hle' hzero'
  have hkk : k' = k := by
    apply le_antisymm
    · by_contra h; exact absurd (hz' k (by omega)) (hpos k le_rfl hkle).ne'
    · by_contra h; exact absurd (hz k' (by omega)) (hpos' k' le_rfl hkl').ne'
  have hll : ℓ' = ℓ := by
    apply le_antisymm
    · by_contra h; exact absurd (hz ℓ' (by omega)) (hpos' ℓ' hkl' le_rfl).ne'
    · by_contra h; exact absurd (hz' ℓ (by omega)) (hpos ℓ hkle le_rfl).ne'
  subst hkk hll
  -- the linear map
  let Φ : (Fin n → ℝ) →ₗ[ℝ] ((Fin (m + 1) → ℝ) × (T → ℝ) × (SmO n k' ℓ' → ℝ)) :=
    { toFun := fun d => (fun i => moment d i.val,
        fun j => ext x (j.val + 1) * ext d (j.val - 1) + ext x (j.val - 1) * ext d (j.val + 1)
          - 2 * ext x j.val * ext d j.val,
        fun o => d o.val)
      map_add' := by
        intro d e
        ext <;> simp [sm_moment_add, sm_ext_add] <;> ring
      map_smul' := by
        intro s d
        ext <;> simp [sm_moment_smul, sm_ext_smul] <;> ring }
  have hcardO : Fintype.card (SmO n k' ℓ') + (ℓ' - k' + 1) ≤ n := by
    have h1 : Fintype.card (SmO n k' ℓ') = n - Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
      have := Fintype.card_subtype_compl (fun j : Fin n => k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ')
      simpa using this
    have h2 : ℓ' - k' + 1 ≤ Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
      have : Fintype.card (Finset.Icc k' ℓ') ≤
          Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} := by
        refine Fintype.card_le_of_injective
          (fun i => (⟨⟨i.1 - 1, by have := Finset.mem_Icc.1 i.2; omega⟩, by
            have := Finset.mem_Icc.1 i.2; simp only; omega⟩ : {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'})) ?_
        intro i1 i2 h
        have h' := congrArg (fun p : {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} => p.1.val) h
        have a1 := Finset.mem_Icc.1 i1.2
        have a2 := Finset.mem_Icc.1 i2.2
        apply Subtype.ext
        simp only at h'
        omega
      have hc : Fintype.card (Finset.Icc k' ℓ') = ℓ' + 1 - k' := by simp
      omega
    have h3 : Fintype.card {j : Fin n // k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ'} ≤ n := by
      simpa using Fintype.card_subtype_le (fun j : Fin n => k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ')
    omega
  have hfin : Module.finrank ℝ ((Fin (m + 1) → ℝ) × (T → ℝ) × (SmO n k' ℓ' → ℝ)) <
      Module.finrank ℝ (Fin n → ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      Fintype.card_coe]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hfin
  obtain ⟨d, hdker, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  have hΦ : Φ d = 0 := hdker
  have hdm : ∀ i ≤ m, moment d i = 0 := by
    intro i hi
    have := congrFun (congrArg Prod.fst hΦ) ⟨i, by omega⟩
    simpa [Φ] using this
  have hdz : ∀ j : Fin n, ¬ (k' ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ') → d j = 0 := by
    intro j hj
    have := congrFun (congrArg (fun p => p.2.2) hΦ) ⟨j, hj⟩
    simpa [Φ] using this
  have hdt : ∀ j, k' < j → j < ℓ' → ext x (j - 1) * ext x (j + 1) = ext x j ^ 2 →
      ext x (j + 1) * ext d (j - 1) + ext x (j - 1) * ext d (j + 1) = 2 * ext x j * ext d j := by
    intro j hj1 hj2 ht
    have hjT : j ∈ T := by rw [hT, Finset.mem_filter, Finset.mem_Ioo]; exact ⟨⟨hj1, hj2⟩, ht⟩
    have := congrFun (congrArg (fun p => p.2.1) hΦ) ⟨j, hjT⟩
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_zero, Prod.fst_zero, Pi.zero_apply] at this
    linarith
  have hev := sm_perturb n m q x d k' ℓ' hk' hkl' hle' hmom hlc' hpos hzero hdm hdz hdt
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  have hp : x + (ε / 2) • d ∈ feasLC n m q := hεb (show dist (ε / 2) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
  have hm : x + (-(ε / 2)) • d ∈ feasLC n m q := hεb (show dist (-(ε / 2)) 0 < ε by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
  have hseg : x ∈ openSegment ℝ (x + (ε / 2) • d) (x + (-(ε / 2)) • d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    simp
    ring
  have := (hextr _ hp _ hm hseg).1
  have h0 : (ε / 2) • d = 0 := by simpa using this
  rcases smul_eq_zero.1 h0 with h | h
  · linarith
  · exact hd0 h
