-- Prove2me | solution 1 for SPOBounds.Natarajan.empirical_rademacher_massart
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:53:12.501552+00:00
-- url     : https://prove2.me/submissions/caaecc98-3fd4-4c17-935c-2998b3a8235d

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SPOBounds_Natarajan_Rademacher
import Definitions.Def_SPOBounds_Natarajan_NatarajanDim

namespace SPOBounds.Natarajan

theorem aux_erm_quad (A B X : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 < t → t * X ≤ A + t ^ 2 * B) : X ≤ Real.sqrt (4 * A * B) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hB with hB0 | hBpos
  · exfalso
    have := h ((A + 1) / X) (by positivity)
    rw [← hB0, div_mul_cancel₀ _ hX.ne'] at this
    linarith
  · have h1 := h (X / (2 * B)) (by positivity)
    have e1 : X / (2 * B) * X = X ^ 2 / (2 * B) := by ring
    have e2 : (X / (2 * B)) ^ 2 * B = X ^ 2 / (4 * B) := by field_simp; ring
    rw [e1, e2] at h1
    have h2 : X ^ 2 / (4 * B) ≤ A := by
      have : X ^ 2 / (2 * B) - X ^ 2 / (4 * B) = X ^ 2 / (4 * B) := by field_simp; ring
      linarith
    rw [div_le_iff₀ (by positivity)] at h2
    have := Real.abs_le_sqrt (x := X) (y := 4 * A * B) (by linarith)
    exact (le_abs_self X).trans this

theorem aux_erm_mgf {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
        Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) ≤
      Real.exp (t ^ 2 * ∑ i, a i ^ 2 / 2) := by
  have h1 : ∀ σ : Fin n → Bool, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * a i) =
      ∏ i, Real.exp (t * ((if σ i then (1 : ℝ) else -1) * a i)) := by
    intro σ; rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i (b : Bool) => Real.exp (t * ((if b then (1 : ℝ) else -1) * a i)))]
  have h2 : ∀ i, ∑ b : Bool, Real.exp (t * ((if b then (1 : ℝ) else -1) * a i)) =
      2 * Real.cosh (t * a i) := by
    intro i
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [if_true, Bool.false_eq_true, if_false]
    ring_nf
  simp_rw [h2]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_assoc,
    one_div, inv_mul_cancel₀ (by positivity), one_mul]
  calc ∏ i, Real.cosh (t * a i) ≤ ∏ i, Real.exp ((t * a i) ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le) (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp (t ^ 2 * ∑ i, a i ^ 2 / 2) := by
        rw [← Real.exp_sum]; congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_); ring

theorem aux_erm_massart {ι : Type*} {n : ℕ} (T : Finset ι) (hT : T.Nonempty)
    (φ : ι → Fin n → ℝ) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ v ∈ T, ∑ i, φ v i ^ 2 ≤ K)
    (g : (Fin n → Bool) → ℝ)
    (hg : ∀ σ, ∃ v ∈ T, g σ ≤ ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :
    (1 / 2 ^ n : ℝ) * ∑ σ, g σ ≤ Real.sqrt (4 * Real.log T.card * (K / 2)) := by
  have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
  apply aux_erm_quad _ _ _ (Real.log_nonneg hcard) (by positivity)
  intro t ht
  set M := (1 / 2 ^ n : ℝ) * ∑ σ, g σ with hM
  -- Jensen
  have hJ : Real.exp (t * M) ≤ ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ) := by
    have hconv := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin n → Bool)))
      (w := fun _ => (1 / 2 ^ n : ℝ)) (p := fun σ => t * g σ)
      (fun _ _ => by positivity) (by simp) (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hconv
    refine le_of_eq_of_le ?_ hconv
    congr 1
    rw [hM, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_); ring
  have hpt : ∀ σ : Fin n → Bool, Real.exp (t * g σ) ≤
      ∑ v ∈ T, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) := by
    intro σ
    obtain ⟨v, hv, hle⟩ := hg σ
    calc Real.exp (t * g σ) ≤ Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle ht.le)
      _ ≤ _ := Finset.single_le_sum (f := fun v =>
            Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i))
            (fun _ _ => (Real.exp_pos _).le) hv
  have hsum : ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ) ≤
      T.card * Real.exp (t ^ 2 * (K / 2)) := by
    calc ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) * Real.exp (t * g σ)
        ≤ ∑ σ : Fin n → Bool, (1 / 2 ^ n : ℝ) *
            ∑ v ∈ T, Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) :=
          Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (hpt σ) (by positivity))
      _ = ∑ v ∈ T, (1 / 2 ^ n : ℝ) * ∑ σ : Fin n → Bool,
            Real.exp (t * ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i) := by
          simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ ≤ ∑ v ∈ T, Real.exp (t ^ 2 * (K / 2)) := by
          refine Finset.sum_le_sum (fun v hv => (aux_erm_mgf (φ v) t).trans ?_)
          refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (sq_nonneg t))
          rw [← Finset.sum_div]; linarith [hK v hv]
      _ = T.card * Real.exp (t ^ 2 * (K / 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hfin : Real.exp (t * M) ≤ Real.exp (Real.log T.card + t ^ 2 * (K / 2)) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
    exact hJ.trans hsum
  exact Real.exp_le_exp.1 hfin

open scoped InnerProductSpace in
theorem aux_erm_gap {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S)
    (c v w0 : EuclideanSpace ℝ (Fin d)) (hv : v ∈ S) (hw0 : w0 ∈ S) :
    ⟪c, v⟫_ℝ - ⟪c, w0⟫_ℝ ≤ linGap S c := by
  have hcont : Continuous (fun u : EuclideanSpace ℝ (Fin d) => ⟪c, u⟫_ℝ) :=
    continuous_const.inner continuous_id
  have hK := hSc.image hcont
  unfold linGap
  have h1 := le_csSup hK.bddAbove (Set.mem_image_of_mem _ hv)
  have h2 := csInf_le hK.bddBelow (Set.mem_image_of_mem _ hw0)
  linarith

open scoped InnerProductSpace in
theorem aux_erm_bddC {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSc : IsCompact S)
    (hS : S.Nonempty) (C : Set (EuclideanSpace ℝ (Fin d))) (hCb : Bornology.IsBounded C) :
    BddAbove (linGap S '' C) := by
  obtain ⟨R, hR⟩ := hCb.exists_norm_le
  obtain ⟨M, hM⟩ := hSc.isBounded.exists_norm_le
  refine ⟨2 * (R * M), ?_⟩
  rintro _ ⟨c, hc, rfl⟩
  have hbound : ∀ v ∈ S, |⟪c, v⟫_ℝ| ≤ R * M := fun v hv =>
    (abs_real_inner_le_norm c v).trans (mul_le_mul (hR c hc) (hM v hv) (norm_nonneg _)
      ((norm_nonneg c).trans (hR c hc)))
  unfold linGap
  have h1 : sSup ((fun v => ⟪c, v⟫_ℝ) '' S) ≤ R * M :=
    csSup_le (hS.image _) (by rintro _ ⟨v, hv, rfl⟩; exact (le_abs_self _).trans (hbound v hv))
  have h2 : -(R * M) ≤ sInf ((fun v => ⟪c, v⟫_ℝ) '' S) :=
    le_csInf (hS.image _) (by
      rintro _ ⟨v, hv, rfl⟩; exact neg_le.2 ((neg_le_abs _).trans (hbound v hv)))
  linarith

end SPOBounds.Natarajan

open SPOBounds.Natarajan
open scoped InnerProductSpace

theorem solution {d : ℕ} {X : Type*}
    (S : Set (EuclideanSpace ℝ (Fin d))) (hS : S.Nonempty) (hSc : IsCompact S)
    (hSv : Convex ℝ S)
    (w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hw : IsOracle S w)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) (hCb : Bornology.IsBounded C)
    (H : Set (X → EuclideanSpace ℝ (Fin d)))
    (n : ℕ) (hn : 0 < n) (s : Fin n → X × EuclideanSpace ℝ (Fin d)) (hsC : ∀ i, (s i).2 ∈ C)
    (hfin : (sampleDecisions w H s).Finite) :
    empRademacherSPO w H s ≤
      linGapSet S C * Real.sqrt (2 * Real.log ((sampleDecisions w H s).ncard : ℝ) / n) := by
  classical
  rcases H.eq_empty_or_nonempty with hH | hH
  · subst hH
    have hV : sampleDecisions w (∅ : Set (X → EuclideanSpace ℝ (Fin d))) s = ∅ := by
      ext v; simp [sampleDecisions]
    have hsup : ∀ σ, signedSup w (∅ : Set (X → EuclideanSpace ℝ (Fin d))) σ s = 0 := by
      intro σ; unfold signedSup; exact Real.iSup_of_isEmpty _
    simp [empRademacherSPO, hsup, hV]
  · set V := sampleDecisions w H s with hVdef
    set T := hfin.toFinset with hTdef
    have hT : T.Nonempty := by
      obtain ⟨f, hf⟩ := hH; exact ⟨_, hfin.mem_toFinset.2 ⟨f, hf, rfl⟩⟩
    set L := linGapSet S C with hLdef
    have hbdd : BddAbove (linGap S '' C) := aux_erm_bddC S hSc hS C hCb
    have hloss : ∀ v ∈ T, ∀ i, 0 ≤ ⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ ∧
        ⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ ≤ L := by
      intro v hv i
      obtain ⟨f, hf, rfl⟩ := hfin.mem_toFinset.1 hv
      refine ⟨sub_nonneg.2 ((hw _).2 _ (hw _).1), ?_⟩
      exact (aux_erm_gap S hSc _ _ _ (hw _).1 (hw _).1).trans
        (le_csSup hbdd (Set.mem_image_of_mem _ (hsC i)))
    have hL : 0 ≤ L := by
      obtain ⟨v, hv⟩ := hT
      exact (hloss v hv ⟨0, hn⟩).1.trans (hloss v hv ⟨0, hn⟩).2
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    let φ : (Fin n → EuclideanSpace ℝ (Fin d)) → Fin n → ℝ :=
      fun v i => (1 / n : ℝ) * (⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ)
    have hK : ∀ v ∈ T, ∑ i, φ v i ^ 2 ≤ L ^ 2 / n := by
      intro v hv
      calc ∑ i, φ v i ^ 2 ≤ ∑ _i : Fin n, (L / n) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            obtain ⟨h0, h1⟩ := hloss v hv i
            have e : φ v i = (⟪(s i).2, v i⟫_ℝ - ⟪(s i).2, w (s i).2⟫_ℝ) / n := by
              simp only [φ]; ring
            rw [e]
            exact pow_le_pow_left₀ (div_nonneg h0 hnR.le) (div_le_div_of_nonneg_right h1 hnR.le) 2
        _ = L ^ 2 / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have hg : ∀ σ : Fin n → Bool, ∃ v ∈ T,
        signedSup w H σ s ≤ ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i := by
      intro σ
      let G : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ :=
        fun v => ∑ i, (if σ i then (1 : ℝ) else -1) * φ v i
      obtain ⟨v0, hv0, heq⟩ := T.exists_mem_eq_sup' hT G
      refine ⟨v0, hv0, ?_⟩
      show signedSup w H σ s ≤ G v0
      rw [← heq]
      unfold signedSup
      have : Nonempty H := hH.to_subtype
      refine ciSup_le (fun f => ?_)
      have hv : (fun i => w (f.1 (s i).1)) ∈ T := hfin.mem_toFinset.2 ⟨f.1, f.2, rfl⟩
      refine le_trans (le_of_eq ?_) (T.le_sup' G hv)
      simp only [G, φ, spoLoss, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have key := aux_erm_massart T hT φ (L ^ 2 / n) (by positivity) hK
      (fun σ => signedSup w H σ s) hg
    rw [Set.ncard_eq_toFinset_card V hfin]
    unfold empRademacherSPO
    refine key.trans (le_of_eq ?_)
    rw [show 4 * Real.log T.card * (L ^ 2 / n / 2) = L ^ 2 * (2 * Real.log T.card / n) by
      field_simp; ring, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL]
