-- Prove2me | solution 1 for ProjNewton.Superlinear.armijo_rhs_positive
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:38:27.851268+00:00
-- url     : https://prove2.me/submissions/a3b90af5-3324-4e08-a994-f0f4f7fa3776

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear
open Matrix Filter Topology Finset

variable {n : ℕ}

lemma arc_apply (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (a : ℝ) (i : Fin n) :
    arc f D x a i = max 0 (x i - a * dir f D x i) := by
  simp [arc, posPart]

lemma herm_symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) (i j : Fin n) :
    D i j = D j i := by
  have := hD.apply i j
  simpa using this.symm

lemma mulVec_restrict {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) {i : Fin n} (hi : i ∉ I) :
    (D *ᵥ g) i = (D *ᵥ (fun j => if j ∈ I then 0 else g j)) i := by
  simp only [mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ I
  · have h1 : D i j = 0 := by
      rw [herm_symm hD]
      exact hdiag j hj i (fun h => hi (h ▸ hj))
    simp [h1, hj]
  · simp [hj]

lemma mulVec_diag {D : Matrix (Fin n) (Fin n) ℝ} {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) {i : Fin n} (hi : i ∈ I) :
    (D *ᵥ g) i = D i i * g i := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hdiag i hi j hji, zero_mul]
  · simp

lemma quad_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) :
    ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i =
      star (fun j => if j ∈ I then 0 else g j) ⬝ᵥ (D *ᵥ (fun j => if j ∈ I then 0 else g j)) := by
  rw [dotProduct, ← Finset.sum_compl_add_sum I]
  rw [Finset.sum_eq_zero (s := I) (fun i hi => by simp [hi]), add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_compl] at hi
  rw [mulVec_restrict hD hdiag g hi]
  simp [hi]

lemma quad_nonneg {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) :
    0 ≤ ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
  rw [quad_eq hD.1 hdiag]
  by_cases h0 : (fun j => if j ∈ I then 0 else g j) = 0
  · rw [h0]; simp
  · exact (hD.dotProduct_mulVec_pos h0).le

lemma quad_pos {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) (h : ∃ i ∉ I, g i ≠ 0) :
    0 < ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
  rw [quad_eq hD.1 hdiag]
  apply hD.dotProduct_mulVec_pos
  obtain ⟨i, hi, hgi⟩ := h
  intro h0
  have := congrFun h0 i
  simp [hi] at this
  exact hgi this

lemma quad_le_zero {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {I : Finset (Fin n)}
    (hdiag : DiagonalWrt D I) (g : Fin n → ℝ) (h : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i ≤ 0) :
    ∀ i ∉ I, g i = 0 := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.mpr (quad_pos hD hdiag g hc))

lemma mem_Iplus (f : Vec n → ℝ) (x : Vec n) (i : Fin n) :
    i ∈ Iplus f x ↔ x i = 0 ∧ 0 < pd f x i := by
  simp [Iplus]

lemma mem_Ik (f : Vec n → ℝ) (μ : Fin n → ℝ) (ε : ℝ) (x : Vec n) (i : Fin n) :
    i ∈ Ik f μ ε x ↔ 0 ≤ x i ∧ x i ≤ min ε (w f μ x) ∧ 0 < pd f x i := by
  simp [Ik]

lemma w_eq_zero_of_critical {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {x : Vec n}
    (hc : IsCritical f x) : w f μ x = 0 := by
  unfold w
  rw [norm_eq_zero, sub_eq_zero]
  ext i
  simp only [posPart, PiLp.toLp_apply, PiLp.sub_apply]
  obtain ⟨hx, hg, hpos⟩ := hc
  have hxi : 0 ≤ x i := hx i
  rcases hxi.lt_or_eq with h | h
  · rw [hpos i h]; simp [h.le]
  · rw [← h]
    have : 0 ≤ μ i * pd f x i := mul_nonneg (hμ i).le (hg i)
    simp [this]

lemma critical_iff {f : Vec n → ℝ} {x : Vec n} (hx : x ∈ orthant n) :
    IsCritical f x ↔ ∀ i ∉ Iplus f x, pd f x i = 0 := by
  constructor
  · rintro ⟨_, hg, hpos⟩ i hi
    rw [mem_Iplus] at hi
    rcases (hx i).lt_or_eq with h | h
    · exact hpos i h
    · have : ¬ 0 < pd f x i := fun h' => hi ⟨h.symm, h'⟩
      linarith [hg i]
  · intro h
    refine ⟨hx, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i ∈ Iplus f x
      · exact ((mem_Iplus f x i).1 hi).2.le
      · exact (h i hi).ge
    · apply h i
      rw [mem_Iplus]
      exact fun h' => (ne_of_gt hi) h'.1

lemma Ik_eq_Iplus_of_critical {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {ε : ℝ}
    (hε : 0 < ε) {x : Vec n} (hc : IsCritical f x) : Ik f μ ε x = Iplus f x := by
  ext i
  rw [mem_Ik, mem_Iplus, w_eq_zero_of_critical hμ hc, min_eq_right hε.le]
  have := hc.1 i
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨le_antisymm h2 h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1.ge, h1.le, h3⟩

lemma fderiv_eq_sum (f : Vec n → ℝ) (x v : Vec n) :
    fderiv ℝ f x v = ∑ i, pd f x i * v i := by
  have : fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    simp [gradient]
  rw [this, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, pd, mul_comm]

/-- general form of the Armijo right-side positivity for arbitrary `a > 0`. -/
lemma rhs_general {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ} (hμ : ∀ i, 0 < μ i) (hε : 0 < ε)
    {x : Vec n} (hx : x ∈ orthant n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) {a : ℝ} (ha : 0 < a) :
    0 ≤ armijoRHS f μ ε D x a ∧ (0 < armijoRHS f μ ε D x a ↔ ¬ IsCritical f x) := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  have hS := quad_nonneg hD hdiag g
  have hp : ∀ i ∈ I, 0 < dir f D x i := by
    intro i hi
    simp only [dir]
    rw [mulVec_diag hdiag _ hi]
    exact mul_pos hD.diag_pos ((mem_Ik f μ ε x i).1 hi).2.2
  have hterm : ∀ i ∈ I, 0 ≤ pd f x i * (x i - arc f D x a i) := by
    intro i hi
    apply mul_nonneg ((mem_Ik f μ ε x i).1 hi).2.2.le
    rw [arc_apply]
    have := hp i hi
    have := hx i
    apply sub_nonneg.mpr
    apply max_le this
    nlinarith
  have hT : 0 ≤ ∑ i ∈ I, pd f x i * (x i - arc f D x a i) := Finset.sum_nonneg hterm
  have hSdef : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := rfl
  have hnn : 0 ≤ armijoRHS f μ ε D x a := by
    unfold armijoRHS
    rw [← hI, hSdef]
    have := mul_nonneg ha.le hS
    linarith
  refine ⟨hnn, ?_, ?_⟩
  · intro hpos hc
    have hIx : ∀ i ∈ I, x i = 0 := by
      intro i hi
      have h := (mem_Ik f μ ε x i).1 hi
      rw [w_eq_zero_of_critical hμ hc, min_eq_right hε.le] at h
      exact le_antisymm h.2.1 h.1
    have hgI : ∀ i ∉ I, pd f x i = 0 := by
      intro i hi
      rw [hI, Ik_eq_Iplus_of_critical hμ hε hc] at hi
      exact (critical_iff hx).1 hc i hi
    have h1 : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hgI i (Finset.mem_compl.1 hi), zero_mul])
    have h2 : ∑ i ∈ I, pd f x i * (x i - arc f D x a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [arc_apply, hIx i hi]
      have := hp i hi
      have : max 0 (0 - a * dir f D x i) = 0 := by
        apply max_eq_left; nlinarith
      rw [this]; ring
    unfold armijoRHS at hpos
    rw [← hI, h1, h2] at hpos
    simp at hpos
  · intro hnc
    by_contra hle
    have h0 : armijoRHS f μ ε D x a = 0 := le_antisymm (not_lt.1 hle) hnn
    unfold armijoRHS at h0
    rw [← hI, hSdef] at h0
    have hS0 : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i = 0 := by
      have := mul_nonneg ha.le hS
      have : a * ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact h
    have hT0 : ∑ i ∈ I, pd f x i * (x i - arc f D x a i) = 0 := by
      rw [hS0, mul_zero, zero_add] at h0; exact h0
    have hgI : ∀ i ∉ I, pd f x i = 0 := quad_le_zero hD hdiag g hS0.le
    have hIx : ∀ i ∈ I, x i = 0 := by
      intro i hi
      have ht := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 hT0 i hi
      have hgpos := ((mem_Ik f μ ε x i).1 hi).2.2
      rcases mul_eq_zero.1 ht with h | h
      · linarith
      · rw [arc_apply] at h
        have := hp i hi
        have hxi := hx i
        by_contra hne
        have hxpos : 0 < x i := lt_of_le_of_ne hxi (Ne.symm hne)
        have : max 0 (x i - a * dir f D x i) < x i := by
          apply max_lt hxpos; nlinarith
        linarith
    apply hnc
    refine ⟨hx, fun i => ?_, fun i hi => ?_⟩
    · by_cases hi : i ∈ I
      · exact ((mem_Ik f μ ε x i).1 hi).2.2.le
      · exact (hgI i hi).ge
    · apply hgI i
      intro hiI
      rw [hIx i hiI] at hi
      exact lt_irrefl _ hi


/-- The direction along which the projected arc is linear for small stepsizes. -/
noncomputable def dvec (x : Vec n) (p : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if 0 < x i then p i else min 0 (p i)

lemma arc_eventually (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) {x : Vec n}
    (hx : x ∈ orthant n) :
    ∀ᶠ a in 𝓝[>] (0:ℝ), arc f D x a = x - a • WithLp.toLp 2 (dvec x (dir f D x)) := by
  have : ∀ᶠ a in 𝓝[>] (0:ℝ), ∀ i, arc f D x a i = x i - a * dvec x (dir f D x) i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hxi : 0 < x i
    · have ht : Tendsto (fun a : ℝ => x i - a * dir f D x i) (𝓝 0) (𝓝 (x i)) := by
        have : Tendsto (fun a : ℝ => x i - a * dir f D x i) (𝓝 0)
            (𝓝 (x i - 0 * dir f D x i)) := by
          exact tendsto_const_nhds.sub (tendsto_id.mul tendsto_const_nhds)
        simpa using this
      have hev := ht.eventually (lt_mem_nhds hxi)
      have hev' : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < x i - a * dir f D x i := nhdsWithin_le_nhds hev
      filter_upwards [hev'] with a ha
      rw [arc_apply, dvec, if_pos hxi, max_eq_right]
      exact ha.le
    · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
      filter_upwards [self_mem_nhdsWithin] with a ha
      have ha' : 0 < a := ha
      rw [arc_apply, dvec, if_neg hxi, hx0]
      rcases le_or_gt 0 (dir f D x i) with hp | hp
      · rw [min_eq_left hp, max_eq_left]
        · ring
        · nlinarith
      · rw [min_eq_right hp.le, max_eq_right]
        nlinarith
  filter_upwards [this] with a ha
  ext i
  rw [ha i]
  simp

lemma tendsto_descent {f : Vec n → ℝ} {x : Vec n} (hf : DifferentiableAt ℝ f x)
    (d : Fin n → ℝ) :
    Tendsto (fun a : ℝ => (f x - f (x - a • WithLp.toLp 2 d)) / a) (𝓝[>] 0)
      (𝓝 (∑ i, pd f x i * d i)) := by
  set v : Vec n := WithLp.toLp 2 d
  have hline : HasDerivAt (fun a : ℝ => x - a • v) (-v) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_sub x
    simpa using this
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x - (0:ℝ) • v) := by
    simpa using hf.hasFDerivAt
  have hcomp := hf'.comp_hasDerivAt (0:ℝ) hline
  rw [hasDerivAt_iff_tendsto_slope] at hcomp
  have hcomp' := (hcomp.mono_left (nhdsWithin_mono _ (fun a (ha : 0 < a) => ne_of_gt ha))).neg
  have heq : -(fderiv ℝ f x (-v)) = ∑ i, pd f x i * d i := by
    rw [map_neg, neg_neg, fderiv_eq_sum]
  rw [heq] at hcomp'
  apply hcomp'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  simp only [slope, Function.comp, vsub_eq_sub, smul_eq_mul, zero_smul, sub_zero]
  rw [div_eq_inv_mul]; ring


lemma dir_pos_of_mem {f : Vec n → ℝ} {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    {I : Finset (Fin n)} (hdiag : DiagonalWrt D I) {x : Vec n} {i : Fin n} (hi : i ∈ I)
    (hg : 0 < pd f x i) : 0 < dir f D x i := by
  simp only [dir]
  rw [mulVec_diag hdiag _ hi]
  exact mul_pos hD.diag_pos hg

lemma prop1a {f : Vec n → ℝ} {x : Vec n} (hx : x ∈ orthant n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Iplus f x))
    (hc : IsCritical f x) : ∀ a : ℝ, 0 ≤ a → arc f D x a = x := by
  intro a ha
  ext i
  rw [arc_apply]
  by_cases hi : i ∈ Iplus f x
  · have hmem := (mem_Iplus f x i).1 hi
    have hp := dir_pos_of_mem hD hdiag hi hmem.2
    rw [hmem.1]
    apply max_eq_left
    nlinarith
  · have : dir f D x i = 0 := by
      simp only [dir]
      rw [mulVec_restrict hD.1 hdiag _ hi]
      have h0 : (fun j => if j ∈ Iplus f x then 0 else pd f x j) = 0 := by
        funext j
        split_ifs with hj
        · rfl
        · exact (critical_iff hx).1 hc j hj
      rw [h0, mulVec_zero]
      rfl
    rw [this, mul_zero, sub_zero, max_eq_right (hx i)]

lemma prop1_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (x : Vec n) (hx : x ∈ orthant n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Iplus f x)) :
    (IsCritical f x ↔ ∀ a : ℝ, 0 ≤ a → arc f D x a = x) ∧
    (¬ IsCritical f x → ∃ abar : ℝ, 0 < abar ∧
      ∀ a ∈ Set.Ioc (0 : ℝ) abar, f (arc f D x a) < f x) := by
  have hdiff : DifferentiableAt ℝ f x := (hf.differentiable one_ne_zero) x
  set I := Iplus f x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  refine ⟨⟨fun hc => prop1a hx hD hdiag hc, fun h => ?_⟩, fun hnc => ?_⟩
  · rw [critical_iff hx]
    apply quad_le_zero hD hdiag g
    apply Finset.sum_nonpos
    intro i hi
    rw [Finset.mem_compl] at hi
    have h1 := congrArg (fun y : Vec n => y i) (h 1 zero_le_one)
    simp only [arc_apply, one_mul] at h1
    have hdir : (D *ᵥ g) i = dir f D x i := rfl
    rw [hdir]
    rcases (hx i).lt_or_eq with hxi | hxi
    · have : x i - dir f D x i = x i := by
        rcases max_choice 0 (x i - dir f D x i) with h' | h' <;> rw [h'] at h1
        · linarith
        · exact h1
      have hp0 : dir f D x i = 0 := by linarith
      rw [hp0, mul_zero]
    · have hp : 0 ≤ dir f D x i := by
        have := le_max_right 0 (x i - dir f D x i)
        rw [h1] at this
        linarith
      have hgi : g i ≤ 0 := by
        by_contra hgi
        exact hi ((mem_Iplus f x i).2 ⟨hxi.symm, lt_of_not_ge hgi⟩)
      nlinarith
  · have hS : 0 < ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i := by
      apply quad_pos hD hdiag g
      by_contra h
      push Not at h
      exact hnc ((critical_iff hx).2 h)
    set d := dvec x (dir f D x) with hd
    have hgd : ∑ i ∈ Iᶜ, g i * (D *ᵥ g) i ≤ ∑ i, pd f x i * d i := by
      rw [← Finset.sum_compl_add_sum I (fun i => pd f x i * d i)]
      have h1 : ∑ i ∈ I, pd f x i * d i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hmem := (mem_Iplus f x i).1 hi
        have hp := dir_pos_of_mem hD hdiag hi hmem.2
        have : d i = 0 := by
          rw [hd, dvec, if_neg (by rw [hmem.1]; exact lt_irrefl 0), min_eq_left hp.le]
        rw [this, mul_zero]
      rw [h1, add_zero]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_compl] at hi
      have hdir : (D *ᵥ g) i = dir f D x i := rfl
      rw [hdir, hd, dvec]
      split_ifs with hxi
      · exact le_rfl
      · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
        have hgi : g i ≤ 0 := by
          by_contra hgi
          exact hi ((mem_Iplus f x i).2 ⟨hx0, lt_of_not_ge hgi⟩)
        exact mul_le_mul_of_nonpos_left (min_le_right _ _) hgi
    have hlim := tendsto_descent hdiff d
    have hev1 := hlim.eventually (lt_mem_nhds (lt_of_lt_of_le hS hgd))
    have hev := hev1.and ((arc_eventually f D hx).and self_mem_nhdsWithin)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
    refine ⟨u, hu, fun a ha => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hsub ha
    have ha0 : 0 < a := h3
    rw [h2]
    have := (div_pos_iff_of_pos_right ha0).1 h1
    linarith

lemma arc_mem_orthant (f : Vec n → ℝ) (D : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (a : ℝ) :
    arc f D x a ∈ orthant n := by
  intro i
  rw [arc_apply]
  exact le_max_left _ _

lemma wd_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) :
    (∀ (x : Vec n), x ∈ orthant n →
      ∀ (D : Matrix (Fin n) (Fin n) ℝ), D.PosDef →
      DiagonalWrt D (Ik f μ ε x) →
      (¬ IsCritical f x → ∃ m₀ : ℕ, ∀ m ≥ m₀, Armijo f μ ε β σ D x m) ∧
      (IsCritical f x → Armijo f μ ε β σ D x 0 ∧ arc f D x 1 = x)) ∧
    (∀ (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n),
      IsRun f μ ε β σ D x → AdmissibleScaling f μ ε D x →
      ∀ k, x k ∈ orthant n ∧
        (¬ IsCritical f (x k) → f (x (k + 1)) < f (x k)) ∧
        (IsCritical f (x k) → x (k + 1) = x k)) := by
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have hσ1 : σ < 1 / 2 := hpar.sigma_mem.2
  have hβ0 : 0 < β := hpar.beta_mem.1
  have hβ1 : β < 1 := hpar.beta_mem.2
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have part1 : ∀ (x : Vec n), x ∈ orthant n →
      ∀ (D : Matrix (Fin n) (Fin n) ℝ), D.PosDef →
      DiagonalWrt D (Ik f μ ε x) →
      (¬ IsCritical f x → ∃ m₀ : ℕ, ∀ m ≥ m₀, Armijo f μ ε β σ D x m) ∧
      (IsCritical f x → Armijo f μ ε β σ D x 0 ∧ arc f D x 1 = x) := by
    intro x hx D hD hdiag
    constructor
    · intro hnc
      set I := Ik f μ ε x with hI
      set d := dvec x (dir f D x) with hd
      set R := ∑ i ∈ Iᶜ, pd f x i * dir f D x i + ∑ i ∈ I, pd f x i * d i with hR
      have hRHS : ∀ᶠ a in 𝓝[>] (0:ℝ), arc f D x a = x - a • WithLp.toLp 2 d ∧
          armijoRHS f μ ε D x a = a * R ∧ 0 < a := by
        filter_upwards [arc_eventually f D hx, self_mem_nhdsWithin] with a ha ha0
        refine ⟨ha, ?_, ha0⟩
        unfold armijoRHS
        rw [← hI, ha]
        have hc : ∀ i, x i - (x - a • WithLp.toLp 2 d : Vec n) i = a * d i := by
          intro i; rw [PiLp.sub_apply, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]; ring
        rw [← hd]
        simp_rw [hc]
        rw [hR, mul_add]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hRpos : 0 < R := by
        obtain ⟨a, ha1, ha2, ha3⟩ := hRHS.exists
        have := (rhs_general hμ hε hx hD hdiag ha3).2.2 hnc
        rw [ha2] at this
        exact (pos_iff_pos_of_mul_pos this).1 ha3
      have hgd : R ≤ ∑ i, pd f x i * d i := by
        rw [← Finset.sum_compl_add_sum I (fun i => pd f x i * d i), hR]
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_compl] at hi
        rw [hd, dvec]
        split_ifs with hxi
        · exact le_rfl
        · have hx0 : x i = 0 := le_antisymm (not_lt.1 hxi) (hx i)
          have hgi : pd f x i ≤ 0 := by
            by_contra hgi
            apply hi
            rw [mem_Ik, hx0]
            exact ⟨le_rfl, le_min hε.le (norm_nonneg _), lt_of_not_ge hgi⟩
          exact mul_le_mul_of_nonpos_left (min_le_right _ _) hgi
      have hlt : σ * R < ∑ i, pd f x i * d i := by nlinarith
      have hlim := tendsto_descent (hdiff x) d
      have hev1 := hlim.eventually (lt_mem_nhds hlt)
      have hP : ∀ᶠ a in 𝓝[>] (0:ℝ),
          σ * armijoRHS f μ ε D x a ≤ f x - f (arc f D x a) := by
        filter_upwards [hev1, hRHS] with a h1 h2
        obtain ⟨h2a, h2b, h2c⟩ := h2
        rw [h2b, h2a]
        rw [lt_div_iff₀ h2c] at h1
        linarith
      have htend : Tendsto (fun m : ℕ => β ^ m) atTop (𝓝[>] (0:ℝ)) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1,
          Filter.Eventually.of_forall (fun m => pow_pos hβ0 m)⟩
      obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (htend.eventually hP)
      exact ⟨m₀, fun m hm => hm₀ m hm⟩
    · intro hc
      have hIk := Ik_eq_Iplus_of_critical hμ hε hc
      have hdiag' : DiagonalWrt D (Iplus f x) := hIk ▸ hdiag
      have harc1 := prop1a hx hD hdiag' hc 1 zero_le_one
      refine ⟨?_, harc1⟩
      unfold Armijo
      rw [pow_zero, harc1, sub_self]
      have h := (rhs_general hμ hε hx hD hdiag one_pos).2
      have hle : armijoRHS f μ ε D x 1 ≤ 0 := not_lt.1 (fun hp => h.1 hp hc)
      nlinarith
  refine ⟨part1, ?_⟩
  intro D x hrun hadm k
  have hxk : ∀ k, x k ∈ orthant n := by
    intro k
    cases k with
    | zero => exact hrun.1
    | succ k =>
      obtain ⟨m, -, -, hx⟩ := hrun.2 k
      rw [hx]
      exact arc_mem_orthant _ _ _ _
  obtain ⟨m, hA, hmin, hnext⟩ := hrun.2 k
  refine ⟨hxk k, fun hnc => ?_, fun hc => ?_⟩
  · have hpos := (rhs_general hμ hε (hxk k) (hadm k).1 (hadm k).2 (pow_pos hβ0 m)).2.2 hnc
    unfold Armijo at hA
    rw [hnext]
    nlinarith [mul_pos hσ0 hpos]
  · have h0 := (part1 _ (hxk k) _ (hadm k).1 (hadm k).2).2 hc
    have hm0 : m = 0 := by
      by_contra hm
      exact hmin 0 (Nat.pos_of_ne_zero hm) h0.1
    rw [hnext, hm0, pow_zero, h0.2]

end ProjNewton.Superlinear

open ProjNewton.Superlinear Matrix Filter Topology

theorem solution {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : Vec n) (hx : x ∈ orthant n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) :
    ∀ m : ℕ, 0 ≤ σ * armijoRHS f μ ε D x (β ^ m) ∧
      (0 < σ * armijoRHS f μ ε D x (β ^ m) ↔ ¬ IsCritical f x) := by
  intro m
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have h := rhs_general hpar.mu_pos hpar.eps_pos hx hD hdiag (pow_pos hpar.beta_mem.1 m)
  refine ⟨mul_nonneg hσ0.le h.1, fun hp => h.2.1 ?_, fun hnc => mul_pos hσ0 (h.2.2 hnc)⟩
  exact (pos_iff_pos_of_mul_pos hp).1 hσ0
