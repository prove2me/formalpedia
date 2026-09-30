-- Prove2me | solution 1 for UnderstandingML.vcDim_linearCombClass_le
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T16:06:07.816987+00:00
-- url     : https://prove2.me/submissions/b6f49a8c-3a67-411b-a245-9626075b3eea

import Definitions.Def_UnderstandingML_Boosting
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite


open MeasureTheory

namespace UnderstandingML

section LinearCombProof

/-- A polynomial form of the Sauer–Shelah lemma: a family of Boolean functions on a finite
type of size `n` that shatters no set of more than `D` points has at most `(n + 1)^D` members. -/
lemma card_le_pow_of_shatter_bound {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (α → Bool)) (D : ℕ)
    (hF : ∀ s : Finset α, (∀ g : α → Bool, ∃ f ∈ F, ∀ a ∈ s, f a = g a) → s.card ≤ D) :
    F.card ≤ (Fintype.card α + 1) ^ D := by
  set 𝒜 : Finset (Finset α) := F.image fun f ↦ Finset.univ.filter fun a ↦ f a = true
  have hinj : Set.InjOn (fun f : α → Bool ↦ Finset.univ.filter fun a ↦ f a = true) F := by
    intro f _ g _ hfg
    funext a
    have := congrArg (a ∈ ·) hfg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
    cases h1 : f a <;> cases h2 : g a <;> simp_all
  have hcard : 𝒜.card = F.card := Finset.card_image_of_injOn hinj
  have hvc : 𝒜.vcDim ≤ D := by
    refine Finset.sup_le fun s hs ↦ ?_
    rw [Finset.mem_shatterer] at hs
    apply hF s
    intro g
    obtain ⟨u, hu, hsu⟩ := hs (Finset.filter_subset (fun a ↦ g a = true) s)
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
    refine ⟨f, hf, fun a ha ↦ ?_⟩
    have := congrArg (a ∈ ·) hsu
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff,
      ha] at this
    cases h1 : f a <;> cases h2 : g a <;> simp_all
  set n := Fintype.card α
  calc F.card = 𝒜.card := hcard.symm
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, n.choose k := Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.range (D + 1), n.choose k := by
        apply Finset.sum_le_sum_of_subset
        intro k hk
        simp only [Finset.mem_Iic] at hk
        simp only [Finset.mem_range]
        omega
    _ ≤ ∑ k ∈ Finset.range (D + 1), n ^ k * 1 ^ (D - k) * D.choose k := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hkD : k ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        have h1 : 1 ≤ D.choose k := Nat.choose_pos hkD
        calc n.choose k ≤ n ^ k := Nat.choose_le_pow n k
          _ ≤ n ^ k * 1 ^ (D - k) * D.choose k := by
            rw [one_pow, mul_one]; exact Nat.le_mul_of_pos_right _ h1
    _ = (n + 1) ^ D := (add_pow n 1 D).symm

/-- Homogeneous halfspaces in `ℝ^T` shatter no set of more than `T` points: `T + 1` vectors are
linearly dependent, and a dependence relation rules out one labeling. -/
lemma halfspace_shatter_card_le {α : Type*} {T : ℕ} (φ : α → Fin T → ℝ) (s : Finset α)
    (hs : ∀ g : α → Bool, ∃ w : Fin T → ℝ, ∀ a ∈ s, decide (0 < ∑ t, w t * φ a t) = g a) :
    s.card ≤ T := by
  classical
  by_contra hlt
  push Not at hlt
  let v : s → (Fin T → ℝ) := fun a ↦ φ a
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun, Fintype.card_coe] at this
    omega
  obtain ⟨c, hc0, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hdep
  -- a dependence relation with a positive coefficient
  obtain ⟨c', hc'0, i', hi'⟩ : ∃ c' : s → ℝ, ∑ j, c' j • v j = 0 ∧ ∃ i', 0 < c' i' := by
    rcases lt_or_gt_of_ne hi with h | h
    · refine ⟨-c, ?_, i, by simpa using h⟩
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, hc0, neg_zero]
    · exact ⟨c, hc0, i, h⟩
  obtain ⟨w, hw⟩ := hs fun a ↦ if h : a ∈ s then decide (0 < c' ⟨a, h⟩) else false
  have hwj : ∀ j : s, decide (0 < ∑ t, w t * v j t) = decide (0 < c' j) := by
    intro j
    have := hw j j.2
    simpa using this
  have hzero : ∑ j : s, c' j * ∑ t, w t * v j t = 0 := by
    have hcoord : ∀ t, ∑ j : s, c' j * v j t = 0 := by
      intro t
      have := congrFun hc'0 t
      simpa [Finset.sum_apply] using this
    calc ∑ j : s, c' j * ∑ t, w t * v j t = ∑ t, w t * ∑ j : s, c' j * v j t := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
          ring
      _ = 0 := Finset.sum_eq_zero fun t _ ↦ by rw [hcoord t, mul_zero]
  have hnn : ∀ j ∈ (Finset.univ : Finset s), 0 ≤ c' j * ∑ t, w t * v j t := by
    intro j _
    have := hwj j
    by_cases hj : 0 < c' j
    · have h2 : 0 < ∑ t, w t * v j t := by simpa [hj] using this
      positivity
    · have h2 : ¬ 0 < ∑ t, w t * v j t := by simpa [hj] using this
      push Not at hj h2
      exact mul_nonneg_of_nonpos_of_nonpos hj h2
  have hpos : 0 < c' i' * ∑ t, w t * v i' t := by
    have h2 : 0 < ∑ t, w t * v i' t := by simpa [hi'] using hwj i'
    positivity
  have := Finset.sum_pos' hnn ⟨i', Finset.mem_univ _, hpos⟩
  linarith

/-- The analytic step: `2^M ≤ (M + 1)^K` with `K ≥ 2` forces `M ≤ K (3 log K + 2)`. -/
lemma le_of_two_pow_le_succ_pow (M K : ℕ) (hK : 2 ≤ K) (h : 2 ^ M ≤ (M + 1) ^ K) :
    (M : ℝ) ≤ K * (3 * Real.log K + 2) := by
  by_contra hlt
  push Not at hlt
  set u := Real.log K with hu_def
  set x0 : ℝ := K * (3 * u + 2) with hx0
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hu : 0 < u := Real.log_pos (by linarith)
  have hln2 := Real.log_two_gt_d9
  have hlog : (M : ℝ) * Real.log 2 ≤ K * Real.log (M + 1) := by
    have h' : ((2 : ℝ) ^ M) ≤ ((M : ℝ) + 1) ^ K := by exact_mod_cast h
    have := Real.log_le_log (by positivity) h'
    rwa [Real.log_pow, Real.log_pow] at this
  have hx0pos : 0 < x0 := by positivity
  have hconc : Real.log (M + 1) ≤ Real.log (x0 + 1) + ((M : ℝ) - x0) / (x0 + 1) := by
    have h1 := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1) / (x0 + 1)) (by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h1
    have h2 : ((M : ℝ) + 1) / (x0 + 1) - 1 = ((M : ℝ) - x0) / (x0 + 1) := by
      field_simp; ring
    linarith
  have hkey : (K : ℝ) * Real.log (x0 + 1) < x0 * Real.log 2 := by
    have h1 : Real.log (x0 + 1) ≤ u + Real.log 3 + Real.log (u + 1) := by
      have hle : x0 + 1 ≤ K * (3 * (u + 1)) := by rw [hx0]; nlinarith
      calc Real.log (x0 + 1) ≤ Real.log (K * (3 * (u + 1))) :=
            Real.log_le_log (by positivity) hle
        _ = u + Real.log 3 + Real.log (u + 1) := by
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity)]
            ring
    have h2 : Real.log (u + 1) ≤ u := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < u + 1 by linarith)]
    have h3 : Real.log 3 < 2 * Real.log 2 := by
      rw [← Real.log_rpow (by norm_num)]
      exact Real.log_lt_log (by norm_num) (by norm_num)
    calc (K : ℝ) * Real.log (x0 + 1) ≤ K * (2 * u + Real.log 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ < K * ((3 * u + 2) * Real.log 2) := by
          apply mul_lt_mul_of_pos_left _ (by positivity); nlinarith
      _ = x0 * Real.log 2 := by rw [hx0]; ring
  have hslope : (K : ℝ) / (x0 + 1) ≤ Real.log 2 := by
    rw [div_le_iff₀ (by positivity), hx0]
    nlinarith
  have h4 : (K : ℝ) * Real.log (M + 1) ≤
      K * Real.log (x0 + 1) + ((M : ℝ) - x0) * (K / (x0 + 1)) := by
    have := mul_le_mul_of_nonneg_left hconc (show (0 : ℝ) ≤ K by positivity)
    have h5 : (K : ℝ) * (((M : ℝ) - x0) / (x0 + 1)) = ((M : ℝ) - x0) * (K / (x0 + 1)) := by
      ring
    linarith
  have h6 : ((M : ℝ) - x0) * (K / (x0 + 1)) ≤ ((M : ℝ) - x0) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hslope (by linarith)
  nlinarith

/-- Restrictions of `B` to a finite set `C` shatter no subset of `C` larger than `VCdim(B)`. -/
lemma restr_shatter_card_le {X : Type*} (B : Set (X → Bool)) (d : ℕ) (hB : vcDim B = d)
    (C : Finset X) (s : Finset C)
    (hs : ∀ g : C → Bool, ∃ f : C → Bool, (∃ b ∈ B, ∀ c, f c = b c) ∧ ∀ a ∈ s, f a = g a) :
    s.card ≤ d := by
  classical
  set s' : Finset X := s.map (Function.Embedding.subtype _) with hs'
  have hsh : Shatters B s' := by
    intro g'
    obtain ⟨f, ⟨b, hb, hfb⟩, hfg⟩ :=
      hs fun c ↦ if h : (c : X) ∈ s' then g' ⟨c, h⟩ else false
    refine ⟨b, hb, fun x ↦ ?_⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
    have := hfg a ha
    rw [hfb] at this
    simp only [Function.Embedding.coe_subtype] at this ⊢
    rw [this]
    split_ifs with h
    · rfl
    · exact absurd hx h
  have h1 : (s'.card : ℕ∞) ≤ vcDim B :=
    le_iSup₂ (f := fun (C : Finset X) (_ : Shatters B C) ↦ (C.card : ℕ∞)) s' hsh
  rw [hB, hs', Finset.card_map] at h1
  exact_mod_cast h1

/-- The counting step of Lemma 10.3: if `L(B, T)` shatters `C` with `|C| = M`, then
`2^M ≤ (M + 1)^{T (d + 1)}`. -/
lemma two_pow_le_of_shatters {X : Type*} (B : Set (X → Bool)) (T d : ℕ) (hB : vcDim B = d)
    (C : Finset X) (hC : Shatters (linearCombClass B T) C) :
    2 ^ C.card ≤ (C.card + 1) ^ (T * (d + 1)) := by
  classical
  set M := C.card with hM
  let RB : Finset (C → Bool) := Finset.univ.filter fun f ↦ ∃ b ∈ B, ∀ c, f c = b c
  let G : (Fin T → C → Bool) → Finset (C → Bool) := fun hs ↦ Finset.univ.filter fun g ↦
    ∃ w : Fin T → ℝ, ∀ c, g c = decide (0 < ∑ t, w t * sgn (hs t c))
  have hRB : RB.card ≤ (M + 1) ^ d := by
    have := card_le_pow_of_shatter_bound RB d fun s hs ↦
      restr_shatter_card_le B d hB C s fun g ↦ by
        obtain ⟨f, hf, hfg⟩ := hs g
        exact ⟨f, (Finset.mem_filter.1 hf).2, hfg⟩
    simpa [M] using this
  have hG : ∀ hs, (G hs).card ≤ (M + 1) ^ T := by
    intro hs
    have := card_le_pow_of_shatter_bound (G hs) T fun s hsh ↦
      halfspace_shatter_card_le (fun c t ↦ sgn (hs t c)) s fun g ↦ by
        obtain ⟨f, hf, hfg⟩ := hsh g
        obtain ⟨w, hw⟩ := (Finset.mem_filter.1 hf).2
        exact ⟨w, fun a ha ↦ by rw [← hw a, hfg a ha]⟩
    simpa [M] using this
  have hcover : (Finset.univ : Finset (C → Bool)) ⊆
      (Fintype.piFinset fun _ : Fin T ↦ RB).biUnion G := by
    intro g _
    obtain ⟨h, ⟨w, hs', hs'B, rfl⟩, hhg⟩ := hC g
    rw [Finset.mem_biUnion]
    refine ⟨fun t c ↦ hs' t c, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro t
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs' t, hs'B t, fun c ↦ rfl⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, w, fun c ↦ (hhg c).symm⟩
  calc 2 ^ M = (Finset.univ : Finset (C → Bool)).card := by simp [M]
    _ ≤ ((Fintype.piFinset fun _ : Fin T ↦ RB).biUnion G).card := Finset.card_le_card hcover
    _ ≤ ∑ hs ∈ Fintype.piFinset (fun _ : Fin T ↦ RB), (G hs).card := Finset.card_biUnion_le
    _ ≤ ∑ hs ∈ Fintype.piFinset (fun _ : Fin T ↦ RB), (M + 1) ^ T :=
        Finset.sum_le_sum fun hs _ ↦ hG hs
    _ = RB.card ^ T * (M + 1) ^ T := by simp [Fintype.card_piFinset]
    _ ≤ ((M + 1) ^ d) ^ T * (M + 1) ^ T := by gcongr
    _ = (M + 1) ^ (T * (d + 1)) := by ring

end LinearCombProof

/-- **Lemma 10.3** (p. 139). Let `B` be a base class and let `L(B, T)` be as defined in Equation
(10.4). Assume that both `T` and `VCdim(B)` are at least `3`. Then
`VCdim(L(B, T)) ≤ T (VCdim(B) + 1)(3 log(T (VCdim(B) + 1)) + 2)` (natural logarithm; the
right-hand side is real, and the VC-dimension is at most its integer part).

The hypotheses `3 ≤ T` and `3 ≤ d` are those of the book and of the milestone statement; the
proof only uses `T (d + 1) ≥ 2`, so `hd` is not referenced. -/
theorem vcDim_linearCombClass_le {X : Type*} (B : Set (X → Bool)) (T d : ℕ) (hT : 3 ≤ T)
    (hd : 3 ≤ d) (hB : vcDim B = d) :
    vcDim (linearCombClass B T) ≤
      (⌊(T * (d + 1) : ℝ) * (3 * Real.log (T * (d + 1)) + 2)⌋₊ : ℕ∞) := by
  have hK : 2 ≤ T * (d + 1) := by nlinarith
  unfold vcDim
  refine iSup₂_le fun C hC ↦ ?_
  have h1 := le_of_two_pow_le_succ_pow C.card (T * (d + 1)) hK
    (two_pow_le_of_shatters B T d hB C hC)
  have h2 : C.card ≤ ⌊(T * (d + 1) : ℝ) * (3 * Real.log (T * (d + 1)) + 2)⌋₊ := by
    apply Nat.le_floor
    push_cast at h1
    exact h1
  exact_mod_cast h2

end UnderstandingML

open UnderstandingML in
theorem solution {X : Type*} (B : Set (X → Bool)) (T d : ℕ) (hT : 3 ≤ T)
    (hd : 3 ≤ d) (hB : vcDim B = d) :
    vcDim (linearCombClass B T) ≤
      (⌊(T * (d + 1) : ℝ) * (3 * Real.log (T * (d + 1)) + 2)⌋₊ : ℕ∞) :=
  UnderstandingML.vcDim_linearCombClass_le B T d hT hd hB
