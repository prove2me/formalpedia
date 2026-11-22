-- Prove2me | solution 1 for ParallelPostulate.Hilbert.archimedes_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:20.122431+00:00
-- url     : https://prove2.me/submissions/2108a97d-9b07-4adb-ad9b-5095cc0b8254

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_between_pt_of_strictBetween
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_one
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_zero


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution {κ : ℝ} (hκ : κ ≤ 0) (len : ℝ × ℝ → ℝ × ℝ → ℝ)
    (hcong : ∀ {P Q R S : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → R ∈ plane κ → S ∈ plane κ →
      (apart κ P Q = apart κ R S ↔ len P Q = len R S))
    (hadd : ∀ {A B C : ℝ × ℝ}, A ∈ plane κ → C ∈ plane κ → Between A B C →
      len A C = len A B + len B C)
    (hpos : ∀ {P Q : ℝ × ℝ}, P ∈ plane κ → Q ∈ plane κ → P ≠ Q → 0 < len P Q)
    (hzero : ∀ {P : ℝ × ℝ}, P ∈ plane κ → len P P = 0)
    (hexist : ∀ {O D : ℝ × ℝ}, O ∈ plane κ → O ≠ D → ∀ d, 0 < d →
      ∃ t, 0 < t ∧ (Dim.mk O D).pt t ∈ plane κ ∧ len O ((Dim.mk O D).pt t) = d) :
    (model κ hκ).Archimedes := by
  intro A B C D hAB hCD
  have hAB' : A.1 ≠ B.1 := fun e => hAB (Subtype.ext e)
  have hM : (Dim.mk A.1 B.1).zero ≠ (Dim.mk A.1 B.1).one := hAB'
  have hpt0 : (Dim.mk A.1 B.1).pt 0 = A.1 := Dim.pt_zero _
  have hpt1 : (Dim.mk A.1 B.1).pt 1 = B.1 := Dim.pt_one _
  have hδ : 0 < len C.1 D.1 := hpos C.2 D.2 (fun e => hCD (Subtype.ext e))
  have hch : ∀ i : ℕ, ∃ t, 0 < t ∧ (Dim.mk A.1 B.1).pt t ∈ plane κ ∧
      len A.1 ((Dim.mk A.1 B.1).pt t) = ((i : ℝ) + 1) * len C.1 D.1 :=
    fun i => hexist A.2 hAB' _ (by positivity)
  choose u hu0 hum hul using hch
  let σ : ℕ → ℝ := fun i => match i with
    | 0 => 0
    | i + 1 => u i
  have hσm : ∀ i, (Dim.mk A.1 B.1).pt (σ i) ∈ plane κ := by
    rintro (_ | i)
    · change (Dim.mk A.1 B.1).pt 0 ∈ plane κ
      rw [hpt0]
      exact A.2
    · exact hum i
  have hσl : ∀ i : ℕ, len A.1 ((Dim.mk A.1 B.1).pt (σ i)) = (i : ℝ) * len C.1 D.1 := by
    rintro (_ | i)
    · change len A.1 ((Dim.mk A.1 B.1).pt 0) = _
      rw [hpt0, hzero A.2]
      simp
    · change len A.1 ((Dim.mk A.1 B.1).pt (u i)) = _
      rw [hul i]
      push_cast
      ring
  have hσ0 : ∀ i, 0 ≤ σ i := by
    rintro (_ | i)
    · exact le_rfl
    · exact (hu0 i).le
  have hmono : ∀ s t : ℝ, 0 ≤ t → (Dim.mk A.1 B.1).pt s ∈ plane κ →
      (Dim.mk A.1 B.1).pt t ∈ plane κ →
      len A.1 ((Dim.mk A.1 B.1).pt s) < len A.1 ((Dim.mk A.1 B.1).pt t) → s < t := by
    intro s t ht hsm htm hlt
    by_contra hts
    rcases (not_lt.mp hts).eq_or_lt with e | e
    · rw [e] at hlt
      exact lt_irrefl _ hlt
    · rcases ht.eq_or_lt with e0 | e0
      · rw [← e0, hpt0, hzero A.2] at hlt
        rw [← e0] at e
        have hne : A.1 ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM (hpt0.trans h))
        linarith [hpos A.2 hsm hne]
      · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨e0, e⟩)
        rw [hpt0] at hb
        have hsum := hadd A.2 hsm hb
        have hne : (Dim.mk A.1 B.1).pt t ≠ (Dim.mk A.1 B.1).pt s :=
          fun h => e.ne (Dim.pt_injective _ hM h)
        linarith [hpos htm hsm hne]
  have hσlt : ∀ i j : ℕ, i < j → σ i < σ j := by
    intro i j hij
    apply hmono _ _ (hσ0 j) (hσm i) (hσm j)
    rw [hσl, hσl]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hδ
  let X : ℕ → Pt κ := fun i => ⟨(Dim.mk A.1 B.1).pt (σ i), hσm i⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (len A.1 B.1 / len C.1 D.1)
  refine ⟨n, X, Subtype.ext hpt0, ?_, ?_, ?_, ?_⟩
  · intro i _
    change apart κ C.1 D.1 = apart κ ((Dim.mk A.1 B.1).pt (σ i)) ((Dim.mk A.1 B.1).pt (σ (i + 1)))
    rw [hcong C.2 D.2 (hσm i) (hσm (i + 1))]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h1 := hσl 1
      change len C.1 D.1 = len ((Dim.mk A.1 B.1).pt 0) ((Dim.mk A.1 B.1).pt (σ 1))
      rw [hpt0, h1]
      simp
    · have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
        (Or.inl ⟨(hσlt 0 i hi : 0 < σ i), hσlt i (i + 1) (by omega)⟩)
      rw [hpt0] at hb
      have hsum := hadd A.2 (hσm (i + 1)) hb
      rw [hσl i, hσl (i + 1)] at hsum
      push_cast at hsum
      linarith
  · intro i _
    exact model_onRay_of hAB' ⟨σ (i + 1), hσlt 0 (i + 1) (by omega), rfl⟩
  · intro i _
    exact between_pt_of_strictBetween (Dim.mk A.1 B.1) hM
      (Or.inl ⟨hσlt i (i + 1) (by omega), hσlt (i + 1) (i + 2) (by omega)⟩)
  · left
    have hB1 : (Dim.mk A.1 B.1).pt 1 ∈ plane κ := by
      rw [hpt1]
      exact B.2
    have h1 : 1 < σ n := by
      apply hmono 1 (σ n) (hσ0 n) hB1 (hσm n)
      rw [hpt1, hσl]
      rwa [div_lt_iff₀ hδ] at hn
    have hb := between_pt_of_strictBetween (Dim.mk A.1 B.1) hM (Or.inl ⟨zero_lt_one, h1⟩)
    rw [hpt0, hpt1] at hb
    exact hb
end ParallelPostulate.Hilbert
