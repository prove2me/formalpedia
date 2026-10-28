-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P07.base_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:57:03.457038+00:00
-- url     : https://prove2.me/submissions/9e42781c-ddb4-4f4f-92bd-c0e6f140d256

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P07_Model
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Independent1.P07

section
variable {I : Type*} [Fintype I] [DecidableEq I] (S : Set (Matrix I I ℂ))

lemma S180B_comb {ι : Type*} (s : Finset ι) (hconv : Convex ℝ S) (s0 : Matrix I I ℂ)
    (hs0 : s0 ∈ S) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (x : ι → Matrix I I ℂ)
    (hx : ∀ i ∈ s, x i ∈ S) :
    ∃ r ∈ S, (((∑ i ∈ s, a i : ℝ)) : ℂ) • r = ∑ i ∈ s, ((a i : ℝ) : ℂ) • x i := by
  by_cases h0 : ∑ i ∈ s, a i = 0
  · refine ⟨s0, hs0, ?_⟩
    have hz : ∀ i ∈ s, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).mp h0
    rw [h0, Finset.sum_eq_zero (fun i hi => by rw [hz i hi]; simp)]; simp
  · have hpos : 0 < ∑ i ∈ s, a i := lt_of_le_of_ne (Finset.sum_nonneg ha) (Ne.symm h0)
    refine ⟨∑ i ∈ s, (a i / ∑ j ∈ s, a j) • x i,
      hconv.sum_mem (fun i hi => div_nonneg (ha i hi) hpos.le)
        (by rw [← Finset.sum_div, div_self h0]) hx, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ h0]

lemma S180B_comb2 (hconv : Convex ℝ S) (s0 : Matrix I I ℂ) (hs0 : s0 ∈ S) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Matrix I I ℂ) (hx : x ∈ S) (hy : y ∈ S) :
    ∃ r ∈ S, ((a + b : ℝ) : ℂ) • r = (a : ℂ) • x + (b : ℂ) • y := by
  obtain ⟨r, hr, e⟩ := S180B_comb S (Finset.univ : Finset (Fin 2)) hconv s0 hs0 ![a, b]
    (by intro i _; fin_cases i <;> simpa) ![x, y] (by intro i _; fin_cases i <;> simpa)
  exact ⟨r, hr, by simpa [Fin.sum_univ_two] using e⟩

lemma S180B_trace {A : Matrix I I ℂ} (htr : ∀ X ∈ S, X.trace = 1) {ap am : ℝ}
    {rp rm : Matrix I I ℂ} (h : BaseDecomposition S A ap am rp rm) :
    A.trace = ((ap - am : ℝ) : ℂ) := by
  obtain ⟨-, -, hrp, hrm, rfl⟩ := h
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, htr _ hrp, htr _ hrm]; simp

lemma S180B_neg (A : Matrix I I ℂ) : baseNorm S (-A) = baseNorm S A := by
  unfold baseNorm; congr 1; ext v
  constructor
  · rintro ⟨ap, am, rp, rm, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    exact ⟨am, ap, rm, rp, ⟨h2, h1, h4, h3, by rw [← neg_neg A, h5]; abel⟩, by ring⟩
  · rintro ⟨ap, am, rp, rm, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    exact ⟨am, ap, rm, rp, ⟨h2, h1, h4, h3, by rw [h5]; abel⟩, by ring⟩

lemma S180B_bdd (A : Matrix I I ℂ) :
    BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am} ∧
    BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = am} := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · rintro v ⟨ap, am, rp, rm, h, rfl⟩; exact add_nonneg h.1 h.2.1
  · rintro v ⟨ap, am, rp, rm, h, rfl⟩; exact h.2.1

lemma S180B_nonneg (A : Matrix I I ℂ) : 0 ≤ baseNorm S A ∧ 0 ≤ baseNeg S A := by
  refine ⟨Real.sInf_nonneg ?_, Real.sInf_nonneg ?_⟩
  · rintro v ⟨ap, am, rp, rm, h, rfl⟩; exact add_nonneg h.1 h.2.1
  · rintro v ⟨ap, am, rp, rm, h, rfl⟩; exact h.2.1

lemma S180B_scale (hconv : Convex ℝ S) {A : Matrix I I ℂ}
    (hne : ∃ ap am rp rm, BaseDecomposition S A ap am rp rm) (s0 : Matrix I I ℂ) (hs0 : s0 ∈ S)
    (c : ℝ) (hc : 0 ≤ c) : baseNorm S ((c : ℂ) • A) ≤ c * baseNorm S A := by
  have hall : ∀ v ∈ {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am},
      baseNorm S ((c : ℂ) • A) ≤ c * v := by
    rintro v ⟨ap, am, rp, rm, ⟨h1, h2, h3, h4, h5⟩, rfl⟩
    refine csInf_le (S180B_bdd S _).1 ⟨c * ap, c * am, rp, rm, ⟨mul_nonneg hc h1,
      mul_nonneg hc h2, h3, h4, ?_⟩, by ring⟩
    rw [h5, smul_sub, smul_smul, smul_smul]; push_cast; rfl
  obtain ⟨ap, am, rp, rm, hd⟩ := hne
  rcases eq_or_lt_of_le hc with h0 | hpos
  · subst h0
    have := hall _ ⟨ap, am, rp, rm, hd, rfl⟩
    simpa using this
  · have : baseNorm S ((c : ℂ) • A) / c ≤ baseNorm S A := by
      refine le_csInf (s := {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am})
        ⟨ap + am, ap, am, rp, rm, hd, rfl⟩ ?_
      intro v hv
      rw [div_le_iff₀ hpos, mul_comm]; exact hall v hv
    rwa [div_le_iff₀ hpos, mul_comm] at this

end

section
variable {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I] (S : Set (Matrix I I ℂ))

lemma S180B_s0 (hS : IsBase S) : ∃ s0, s0 ∈ S := by
  by_contra h
  push Not at h
  have hS0 : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
  have h1 := hS.2.2.2 1 Matrix.isHermitian_one
  rw [hS0, Submodule.span_empty, Submodule.mem_bot] at h1
  exact one_ne_zero h1

lemma S180B_exists (hS : IsBase S) {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    ∃ ap am rp rm, BaseDecomposition S A ap am rp rm := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.mp (hS.2.2.2 A hA)
  obtain ⟨rp, hrp, ep⟩ := S180B_comb S Finset.univ hS.2.1 s0 hs0 (fun i => max (f i) 0)
    (fun i _ => le_max_right _ _) (fun i => (g i : Matrix I I ℂ)) (fun i _ => (g i).2)
  obtain ⟨rm, hrm, em⟩ := S180B_comb S Finset.univ hS.2.1 s0 hs0 (fun i => max (-f i) 0)
    (fun i _ => le_max_right _ _) (fun i => (g i : Matrix I I ℂ)) (fun i _ => (g i).2)
  refine ⟨∑ i, max (f i) 0, ∑ i, max (-f i) 0, rp, rm,
    ⟨Finset.sum_nonneg (fun i _ => le_max_right _ _),
    Finset.sum_nonneg (fun i _ => le_max_right _ _), hrp, hrm, ?_⟩⟩
  rw [ep, em, ← hfg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_smul, ← Complex.ofReal_sub, Complex.coe_smul]
  congr 1
  rcases le_total 0 (f i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma S180B_zero (hS : IsBase S) : baseNorm S 0 = 0 := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  refine le_antisymm ?_ (S180B_nonneg S 0).1
  exact csInf_le (S180B_bdd S _).1 ⟨0, 0, s0, s0, ⟨le_rfl, le_rfl, hs0, hs0, by simp⟩, by ring⟩

lemma S180B_eq_zero (hS : IsBase S) {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (h : baseNorm S A = 0) : A = 0 := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  ext i j
  obtain ⟨M, hM⟩ := hS.1.exists_bound_of_continuousOn
    (f := fun X : Matrix I I ℂ => X i j) ((continuous_apply j).comp (continuous_apply i)).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s0 hs0)
  have key : ∀ ε > 0, ‖A i j‖ ≤ ε * M := by
    intro ε hε
    obtain ⟨ap0, am0, rp0, rm0, hd0⟩ := S180B_exists S hS hA
    obtain ⟨v, ⟨ap, am, rp, rm, ⟨h1, h2, h3, h4, h5⟩, hveq⟩, hv⟩ :=
      Real.lt_sInf_add_pos
        (s := {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am})
        ⟨ap0 + am0, ap0, am0, rp0, rm0, hd0, rfl⟩ hε
    subst hveq
    have hv' : ap + am < ε := by
      have : sInf {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am} = 0 := h
      linarith
    rw [h5]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    calc ‖(ap : ℂ) * rp i j - (am : ℂ) * rm i j‖ ≤ ap * M + am * M := by
          refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
            exact mul_le_mul_of_nonneg_left (hM _ h3) h1
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
            exact mul_le_mul_of_nonneg_left (hM _ h4) h2
      _ = (ap + am) * M := by ring
      _ ≤ ε * M := mul_le_mul_of_nonneg_right hv'.le hM0
  have : ‖A i j‖ ≤ 0 := by
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hM0 with hM0' | hMpos
    · have := key 1 one_pos; rw [← hM0', mul_zero] at this; linarith
    · have := key (‖A i j‖ / (2 * M)) (by positivity)
      rw [div_mul_eq_mul_div, mul_div_assoc, div_mul_eq_div_div] at this
      field_simp at this
      linarith
  simpa using norm_le_zero_iff.mp this

lemma S180B_trace_one (hS : IsBase S) {A : Matrix I I ℂ} (hA : A.IsHermitian) (htr : A.trace = 1) :
    baseNorm S A = 1 + 2 * baseNeg S A := by
  have htrS : ∀ X ∈ S, X.trace = 1 := fun X hX => (hS.2.2.1 X hX).2
  have rel : ∀ ap am rp rm, BaseDecomposition S A ap am rp rm → ap = 1 + am := by
    intro ap am rp rm hd
    have := S180B_trace S htrS hd
    rw [htr] at this
    have := congrArg Complex.re this
    simp at this; linarith
  obtain ⟨ap0, am0, rp0, rm0, hd0⟩ := S180B_exists S hS hA
  apply le_antisymm
  · have : (baseNorm S A - 1) / 2 ≤ baseNeg S A := by
      refine le_csInf (s := {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = am})
        ⟨am0, ap0, am0, rp0, rm0, hd0, rfl⟩ ?_
      rintro g ⟨ap, am, rp, rm, hd, hg⟩
      rw [hg]
      have := csInf_le (S180B_bdd S A).1 ⟨ap, am, rp, rm, hd, rfl⟩
      have := rel ap am rp rm hd
      change baseNorm S A ≤ _ at *
      linarith
    linarith
  · have : 1 + 2 * baseNeg S A ≤ baseNorm S A := by
      have : (2 : ℝ)⁻¹ * (baseNorm S A - 1) ≥ baseNeg S A := by
        refine le_trans ?_ (le_of_eq rfl)
        have hle : baseNeg S A ≤ (2 : ℝ)⁻¹ * (baseNorm S A - 1) := by
          rw [← sub_nonneg]
          have : ∀ v ∈ {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am},
              1 + 2 * baseNeg S A ≤ v := by
            rintro v ⟨ap, am, rp, rm, hd, rfl⟩
            have := csInf_le (S180B_bdd S A).2 ⟨ap, am, rp, rm, hd, rfl⟩
            have := rel ap am rp rm hd
            change baseNeg S A ≤ _ at *
            linarith
          have := le_csInf (s := {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am})
            ⟨ap0 + am0, ap0, am0, rp0, rm0, hd0, rfl⟩ this
          change _ ≤ baseNorm S A at this
          linarith
        exact hle
      linarith
    exact this

lemma S180B_tri (hS : IsBase S) {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    baseNorm S (A + B) ≤ baseNorm S A + baseNorm S B := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  have key : ∀ v ∈ {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am},
      ∀ w ∈ {v | ∃ ap am rp rm, BaseDecomposition S B ap am rp rm ∧ v = ap+am},
      baseNorm S (A + B) ≤ v + w := by
    rintro v ⟨ap, am, rp, rm, ⟨a1, a2, a3, a4, a5⟩, rfl⟩ w ⟨bp, bm, sp, sm, ⟨b1, b2, b3, b4, b5⟩, rfl⟩
    obtain ⟨tp, htp, etp⟩ := S180B_comb2 S hS.2.1 s0 hs0 ap bp a1 b1 rp sp a3 b3
    obtain ⟨tm, htm, etm⟩ := S180B_comb2 S hS.2.1 s0 hs0 am bm a2 b2 rm sm a4 b4
    refine csInf_le (S180B_bdd S _).1 ⟨ap + bp, am + bm, tp, tm, ⟨add_nonneg a1 b1,
      add_nonneg a2 b2, htp, htm, ?_⟩, by ring⟩
    rw [etp, etm, a5, b5]; abel
  obtain ⟨ap0, am0, rp0, rm0, hd0⟩ := S180B_exists S hS hA
  obtain ⟨bp0, bm0, sp0, sm0, he0⟩ := S180B_exists S hS hB
  have h1 : ∀ w ∈ {v | ∃ ap am rp rm, BaseDecomposition S B ap am rp rm ∧ v = ap+am},
      baseNorm S (A + B) - w ≤ baseNorm S A := by
    intro w hw
    refine le_csInf (s := {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am})
      ⟨ap0 + am0, ap0, am0, rp0, rm0, hd0, rfl⟩ ?_
    intro v hv; have := key v hv w hw; linarith
  have h2 : baseNorm S (A + B) - baseNorm S A ≤ baseNorm S B := by
    refine le_csInf (s := {v | ∃ ap am rp rm, BaseDecomposition S B ap am rp rm ∧ v = ap+am})
      ⟨bp0 + bm0, bp0, bm0, sp0, sm0, he0, rfl⟩ ?_
    intro w hw; have := h1 w hw; linarith
  linarith

lemma S180B_homog (hS : IsBase S) {A : Matrix I I ℂ} (hA : A.IsHermitian) (t : ℝ) :
    baseNorm S ((t : ℂ) • A) = |t| * baseNorm S A := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  have pos : ∀ (B : Matrix I I ℂ), B.IsHermitian → ∀ c : ℝ, 0 < c →
      baseNorm S ((c : ℂ) • B) = c * baseNorm S B := by
    intro B hB c hc
    apply le_antisymm (S180B_scale S hS.2.1 (S180B_exists S hS hB) s0 hs0 c hc.le)
    have hcB : ((c : ℂ) • B).IsHermitian := by
      have e : ((c : ℂ) • B) = c • B := Complex.coe_smul c B
      rw [e]
      show (c • B)ᴴ = c • B
      rw [Matrix.conjTranspose_smul, hB.eq, star_trivial]
    have := S180B_scale S hS.2.1 (S180B_exists S hS hcB) s0 hs0 c⁻¹ (inv_nonneg.2 hc.le)
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_smul]
      at this
    have := mul_le_mul_of_nonneg_left this hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have e : (t : ℂ) • A = ((|t| : ℝ) : ℂ) • (-A) := by
      rw [abs_of_neg ht, smul_neg, Complex.ofReal_neg, neg_smul, neg_neg]
    rw [e, pos (-A) hA.neg |t| (abs_pos.2 ht.ne), S180B_neg]
  · subst ht; simp [S180B_zero S hS]
  · rw [pos A hA t ht, abs_of_pos ht]

lemma S180B_convex (hS : IsBase S) (q : ℕ) (p : Fin q → ℝ) (A : Fin q → Matrix I I ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hA : ∀ i, (A i).IsHermitian) :
    baseNeg S (∑ i, (p i : ℂ) • A i) ≤ ∑ i, p i * baseNeg S (A i) := by
  obtain ⟨s0, hs0⟩ := S180B_s0 S hS
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hch : ∀ i, ∃ ap am rp rm, BaseDecomposition S (A i) ap am rp rm ∧
      am < baseNeg S (A i) + ε := by
    intro i
    obtain ⟨ap, am, rp, rm, hd⟩ := S180B_exists S hS (hA i)
    obtain ⟨v, ⟨ap', am', rp', rm', hd', hveq⟩, hv⟩ :=
      Real.lt_sInf_add_pos (s := {v | ∃ ap am rp rm, BaseDecomposition S (A i) ap am rp rm ∧ v = am})
        ⟨am, ap, am, rp, rm, hd, rfl⟩ hε
    exact ⟨ap', am', rp', rm', hd', hveq ▸ hv⟩
  choose ap am rp rm hd hlt using hch
  obtain ⟨tp, htp, etp⟩ := S180B_comb S Finset.univ hS.2.1 s0 hs0 (fun i => p i * ap i)
    (fun i _ => mul_nonneg (hp i) (hd i).1) rp (fun i _ => (hd i).2.2.1)
  obtain ⟨tm, htm, etm⟩ := S180B_comb S Finset.univ hS.2.1 s0 hs0 (fun i => p i * am i)
    (fun i _ => mul_nonneg (hp i) (hd i).2.1) rm (fun i _ => (hd i).2.2.2.1)
  have hdec : BaseDecomposition S (∑ i, (p i : ℂ) • A i) (∑ i, p i * ap i) (∑ i, p i * am i)
      tp tm := by
    refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hd i).1),
      Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hd i).2.1), htp, htm, ?_⟩
    rw [etp, etm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hd i).2.2.2.2, smul_sub, smul_smul, smul_smul]; push_cast; rfl
  have h1 := csInf_le (S180B_bdd S _).2 ⟨_, _, _, _, hdec, rfl⟩
  change baseNeg S _ ≤ _ at h1
  have h2 : ∑ i, p i * am i ≤ ∑ i, p i * (baseNeg S (A i) + ε) :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlt i).le (hp i))
  have h3 : ∑ i, p i * (baseNeg S (A i) + ε) = ∑ i, p i * baseNeg S (A i) + ε := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
  linarith

theorem solution {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (S : Set (Matrix I I ℂ)) (hS : IsBase S) :
    (∀ A : Matrix I I ℂ, A.IsHermitian →
      (∃ ap am rp rm, BaseDecomposition S A ap am rp rm) ∧
      BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = ap+am} ∧
      BddBelow {v | ∃ ap am rp rm, BaseDecomposition S A ap am rp rm ∧ v = am} ∧
      0 ≤ baseNorm S A ∧ (baseNorm S A = 0 ↔ A = 0) ∧ 0 ≤ baseNeg S A ∧
      (A.trace = 1 → baseNorm S A = 1+2*baseNeg S A)) ∧
    (∀ (A B : Matrix I I ℂ), A.IsHermitian → B.IsHermitian →
      baseNorm S (A+B) ≤ baseNorm S A+baseNorm S B) ∧
    (∀ (A : Matrix I I ℂ) (t : ℝ), A.IsHermitian →
      baseNorm S ((t : ℂ) • A) = |t| * baseNorm S A) ∧
    (∀ (q : ℕ) (p : Fin q → ℝ) (A : Fin q → Matrix I I ℂ),
      (∀ i, 0 ≤ p i) → (∑ i, p i = 1) → (∀ i, (A i).IsHermitian) →
      baseNeg S (∑ i, (p i : ℂ) • A i) ≤ ∑ i, p i*baseNeg S (A i)) := by
  refine ⟨fun A hA => ⟨S180B_exists S hS hA, (S180B_bdd S A).1, (S180B_bdd S A).2,
    (S180B_nonneg S A).1, ⟨S180B_eq_zero S hS hA, fun h => by rw [h]; exact S180B_zero S hS⟩,
    (S180B_nonneg S A).2, S180B_trace_one S hS hA⟩,
    fun A B hA hB => S180B_tri S hS hA hB, fun A t hA => S180B_homog S hS hA t,
    fun q p A hp hp1 hA => S180B_convex S hS q p A hp hp1 hA⟩

end
