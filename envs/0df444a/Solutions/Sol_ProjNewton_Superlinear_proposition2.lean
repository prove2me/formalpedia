-- Prove2me | solution 1 for ProjNewton.Superlinear.proposition2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:49:26.03089+00:00
-- url     : https://prove2.me/submissions/00d8b198-a96c-4cd5-9def-0bdd7575f16c

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



lemma dot_symm {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian) (u v : Fin n → ℝ) :
    u ⬝ᵥ (D *ᵥ v) = v ⬝ᵥ (D *ᵥ u) := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [herm_symm hD i j]; ring

lemma cs_form {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hnn : ∀ u : Fin n → ℝ, 0 ≤ u ⬝ᵥ (D *ᵥ u)) {c : ℝ} (hc : 0 < c)
    (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c * (u ⬝ᵥ u)) (z : Fin n → ℝ) :
    (D *ᵥ z) ⬝ᵥ (D *ᵥ z) ≤ c * (z ⬝ᵥ (D *ᵥ z)) := by
  set v := D *ᵥ z
  set A := z ⬝ᵥ (D *ᵥ z)
  set B := v ⬝ᵥ v
  set C := v ⬝ᵥ (D *ᵥ v)
  have hzv : z ⬝ᵥ (D *ᵥ v) = B := by
    rw [dot_symm hD]
  have hexp : ∀ t : ℝ, (z + t • v) ⬝ᵥ (D *ᵥ (z + t • v)) = A + 2 * t * B + t ^ 2 * C := by
    intro t
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul]
    rw [hzv]
    have : v ⬝ᵥ (D *ᵥ z) = B := rfl
    rw [this]; ring
  have h1 := hnn (z + (-1 / c) • v)
  rw [hexp] at h1
  have hC : C ≤ c * B := hup v
  have : A + 2 * (-1 / c) * B + (-1 / c) ^ 2 * (c * B) ≥ 0 := by
    have : (-1 / c) ^ 2 * C ≤ (-1 / c) ^ 2 * (c * B) :=
      mul_le_mul_of_nonneg_left hC (sq_nonneg _)
    linarith
  have heq : A + 2 * (-1 / c) * B + (-1 / c) ^ 2 * (c * B) = A - B / c := by
    field_simp; ring
  rw [heq] at this
  have : B / c ≤ A := by linarith
  rw [div_le_iff₀ hc] at this
  linarith


lemma descent {f : Vec n → ℝ} (hf : Differentiable ℝ f) {S : Set (Vec n)} (hS : Convex ℝ S)
    {L : NNReal} (hL : LipschitzOnWith L (gradient f) S) {y z : Vec n} (hy : y ∈ S) (hz : z ∈ S) :
    f z ≤ f y + ∑ i, pd f y i * (z - y) i + L * ‖z - y‖ ^ 2 := by
  set v := z - y
  set φ : ℝ → ℝ := fun t => f (y + t • v)
  have hderiv : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ f (y + t • v) v) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => y + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    exact (hf (y + t • v)).hasFDerivAt.comp_hasDerivAt t hl
  have hcont : ContinuousOn φ (Set.Icc 0 1) :=
    (continuous_iff_continuousAt.2 (fun t => (hderiv t).continuousAt)).continuousOn
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope φ (fun t => fderiv ℝ f (y + t • v) v)
    zero_lt_one hcont (fun t _ => hderiv t)
  have h1 : φ 1 = f z := by simp [φ, v]
  have h0 : φ 0 = f y := by simp [φ]
  rw [h1, h0, sub_zero, div_one] at hceq
  have hmem : y + c • v ∈ S := by
    have := hS.add_smul_sub_mem hy hz ⟨hc.1.le, hc.2.le⟩
    simpa [v] using this
  have hfd : ∀ u : Vec n, fderiv ℝ f u v = inner ℝ (gradient f u) v := by
    intro u; simp [gradient]
  rw [hfd] at hceq
  have hlin : ∑ i, pd f y i * v i = inner ℝ (gradient f y) v := by
    rw [← fderiv_eq_sum, hfd]
  rw [hlin]
  have hdiff : inner ℝ (gradient f (y + c • v)) v - inner ℝ (gradient f y) v ≤ L * ‖v‖ ^ 2 := by
    rw [← inner_sub_left]
    calc inner ℝ (gradient f (y + c • v) - gradient f y) v
        ≤ ‖gradient f (y + c • v) - gradient f y‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖(y + c • v) - y‖) * ‖v‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have := hL.dist_le_mul _ hmem _ hy
          simpa [dist_eq_norm] using this
      _ ≤ L * ‖v‖ ^ 2 := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
          have hL0 : (0:ℝ) ≤ L := L.2
          have : c * ‖v‖ ≤ ‖v‖ := by nlinarith [norm_nonneg v, hc.2]
          have := mul_le_mul_of_nonneg_left this hL0
          nlinarith [norm_nonneg v]
  linarith


lemma posdef_nonneg {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (u : Fin n → ℝ) :
    0 ≤ u ⬝ᵥ (D *ᵥ u) := by
  by_cases hu : u = 0
  · rw [hu]; simp
  · have := hD.dotProduct_mulVec_pos hu
    simpa using this.le

lemma diag_le {D : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c * (u ⬝ᵥ u)) (i : Fin n) : D i i ≤ c := by
  have := hup (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

lemma diag_ge {D : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hlo : ∀ u : Fin n → ℝ, c * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D *ᵥ u)) (i : Fin n) : c ≤ D i i := by
  have := hlo (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using this

lemma grad_dot (f : Vec n → ℝ) (x : Vec n) :
    (fun i => pd f x i) ⬝ᵥ (fun i => pd f x i) = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [dotProduct, pd, sq]

lemma norm_sq_vec (v : Vec n) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp

lemma sub_max_eq_min (x q : ℝ) : x - max 0 (x - q) = min x q := by
  rcases le_total 0 (x - q) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

lemma armijo_of_small {f : Vec n → ℝ} (hf : Differentiable ℝ f) {μ : Fin n → ℝ} {ε σ : ℝ}
    (hμ : ∀ i, 0 < μ i) (hε : 0 < ε)
    (hσ : σ ≤ 1) {x xbar : Vec n} (hx : x ∈ orthant n) (hxb : ‖x - xbar‖ ≤ 1)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Ik f μ ε x))
    {c2 : ℝ} (hc2 : 0 < c2) (hup : ∀ u : Fin n → ℝ, u ⬝ᵥ (D *ᵥ u) ≤ c2 * (u ⬝ᵥ u))
    {G : ℝ} (hG : ‖gradient f x‖ ≤ G) {εbar : ℝ} (hεbar : εbar ≤ min ε (w f μ x))
    {L : NNReal} (hL : LipschitzOnWith L (gradient f) (Metric.closedBall xbar (1 + c2 * G)))
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (haε : a * (c2 * G) ≤ εbar)
    (haL : a * (L * c2) ≤ 1 - σ) :
    σ * armijoRHS f μ ε D x a ≤ f x - f (arc f D x a) := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun i => pd f x i with hg
  set p : Fin n → ℝ := dir f D x with hp
  have hpg : p = D *ᵥ g := rfl
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) hG
  have hnn := posdef_nonneg hD
  have hgg : g ⬝ᵥ g ≤ G ^ 2 := by
    rw [hg, grad_dot]; exact pow_le_pow_left₀ (norm_nonneg _) hG 2
  have hpp : p ⬝ᵥ p ≤ (c2 * G) ^ 2 := by
    rw [hpg]
    have h1 := cs_form hD.1 hnn hc2 hup g
    have h2 := hup g
    have h3 : c2 * (g ⬝ᵥ (D *ᵥ g)) ≤ c2 * (c2 * (g ⬝ᵥ g)) := mul_le_mul_of_nonneg_left h2 hc2.le
    have h4 : c2 * (c2 * (g ⬝ᵥ g)) ≤ c2 * (c2 * G ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgg hc2.le) hc2.le
    nlinarith
  have hpi : ∀ i, |p i| ≤ c2 * G := by
    intro i
    have : p i ^ 2 ≤ p ⬝ᵥ p := by
      have := Finset.single_le_sum (f := fun j => p j * p j) (fun j _ => mul_self_nonneg (p j))
        (Finset.mem_univ i)
      simpa [dotProduct, sq] using this
    have hK : 0 ≤ c2 * G := mul_nonneg hc2.le hG0
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  set e : Fin n → ℝ := fun i => x i - arc f D x a i with he
  have he_min : ∀ i, e i = min (x i) (a * p i) := by
    intro i; simp only [he]; rw [arc_apply, sub_max_eq_min]
  have he_sq : ∀ i, e i ^ 2 ≤ a ^ 2 * p i ^ 2 := by
    intro i
    rw [he_min]
    have hxi := hx i
    rcases le_total (x i) (a * p i) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  -- Key 1
  have hlin : armijoRHS f μ ε D x a ≤ ∑ i, g i * e i := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => g i * e i)]
    apply add_le_add _ le_rfl
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_compl] at hi
    show a * (g i * p i) ≤ g i * e i
    rw [he_min]
    rcases le_total (a * p i) (x i) with h | h
    · rw [min_eq_right h]; ring_nf; exact le_rfl
    · rw [min_eq_left h]
      rcases le_or_gt (g i) 0 with hgi | hgi
      · nlinarith
      · exfalso
        apply hi
        rw [mem_Ik]
        refine ⟨hx i, ?_, hgi⟩
        have := hpi i
        have : a * p i ≤ a * (c2 * G) := by
          have := le_abs_self (p i)
          nlinarith
        linarith
  -- Key 2
  have hsq : ∑ i, e i ^ 2 ≤ a * c2 * armijoRHS f μ ε D x a := by
    unfold armijoRHS
    rw [← hI, ← Finset.sum_compl_add_sum I (fun i => e i ^ 2)]
    set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j
    have hS : ∑ i ∈ Iᶜ, pd f x i * dir f D x i = gJ ⬝ᵥ (D *ᵥ gJ) := by
      have := quad_eq hD.1 hdiag g
      simp only [star_trivial] at this
      exact this
    have hA : ∑ i ∈ Iᶜ, e i ^ 2 ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) := by
      calc ∑ i ∈ Iᶜ, e i ^ 2 ≤ ∑ i ∈ Iᶜ, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * ∑ i ∈ Iᶜ, (D *ᵥ gJ) i ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_compl] at hi
            rw [hpg, mulVec_restrict hD.1 hdiag g hi]
        _ ≤ a ^ 2 * ((D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
            have : (D *ᵥ gJ) ⬝ᵥ (D *ᵥ gJ) = ∑ i, (D *ᵥ gJ) i ^ 2 := by
              simp [dotProduct, sq]
            rw [this]
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun i _ _ => sq_nonneg _)
        _ ≤ a ^ 2 * (c2 * (gJ ⬝ᵥ (D *ᵥ gJ))) :=
            mul_le_mul_of_nonneg_left (cs_form hD.1 hnn hc2 hup gJ) (sq_nonneg a)
    have hB : ∑ i ∈ I, e i ^ 2 ≤ a * c2 * ∑ i ∈ I, pd f x i * (x i - arc f D x a i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hgi := ((mem_Ik f μ ε x i).1 hi).2.2
      have hpi' : p i = D i i * g i := by rw [hpg, mulVec_diag hdiag g hi]
      have hDii := diag_le hup i
      have hDpos : 0 < D i i := hD.diag_pos
      show e i ^ 2 ≤ a * c2 * (g i * e i)
      have he0 : 0 ≤ e i := by
        rw [he_min]; exact le_min (hx i) (by rw [hpi']; positivity)
      have hle : e i ≤ a * p i := by rw [he_min]; exact min_le_right _ _
      have h1 : e i ^ 2 ≤ e i * (a * p i) := by nlinarith
      rw [hpi'] at h1
      have h2 : e i * (a * (D i i * g i)) ≤ e i * (a * (c2 * g i)) := by
        apply mul_le_mul_of_nonneg_left _ he0
        apply mul_le_mul_of_nonneg_left _ ha.le
        exact mul_le_mul_of_nonneg_right hDii hgi.le
      nlinarith
    rw [hS]
    nlinarith
  -- Key 3: membership in the ball
  have hnorm : ‖arc f D x a - x‖ ^ 2 = ∑ i, e i ^ 2 := by
    rw [norm_sq_vec]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, PiLp.sub_apply]
    ring
  have hsmall : ‖arc f D x a - x‖ ≤ c2 * G := by
    have h1 : ∑ i, e i ^ 2 ≤ (c2 * G) ^ 2 := by
      calc ∑ i, e i ^ 2 ≤ ∑ i, a ^ 2 * p i ^ 2 := Finset.sum_le_sum (fun i _ => he_sq i)
        _ = a ^ 2 * (p ⬝ᵥ p) := by rw [dotProduct, Finset.mul_sum]; simp [sq]
        _ ≤ 1 * (p ⬝ᵥ p) := by
            have hpp0 : 0 ≤ p ⬝ᵥ p := Finset.sum_nonneg (fun j _ => mul_self_nonneg (p j))
            apply mul_le_mul_of_nonneg_right _ hpp0
            nlinarith
        _ ≤ (c2 * G) ^ 2 := by linarith
    rw [← hnorm] at h1
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc2.le hG0) two_ne_zero).1 h1
  have hxmem : x ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    nlinarith [mul_nonneg hc2.le hG0]
  have harcmem : arc f D x a ∈ Metric.closedBall xbar (1 + c2 * G) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc ‖arc f D x a - xbar‖ = ‖(arc f D x a - x) + (x - xbar)‖ := by congr 1; abel
      _ ≤ ‖arc f D x a - x‖ + ‖x - xbar‖ := norm_add_le _ _
      _ ≤ 1 + c2 * G := by linarith
  -- Key 4: descent
  have hdes := descent hf (convex_closedBall xbar (1 + c2 * G)) hL hxmem harcmem
  have hlin2 : ∑ i, pd f x i * (arc f D x a - x) i = -∑ i, g i * e i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [he, hg, PiLp.sub_apply]
    ring
  rw [hlin2, hnorm] at hdes
  have hRHS0 := (rhs_general hμ hε hx hD hdiag ha).1
  have hL0 : (0:ℝ) ≤ L := L.2
  have h5 : (L:ℝ) * ∑ i, e i ^ 2 ≤ L * (a * c2 * armijoRHS f μ ε D x a) :=
    mul_le_mul_of_nonneg_left hsq hL0
  have h6 : σ * armijoRHS f μ ε D x a ≤ (1 - a * (L * c2)) * armijoRHS f μ ε D x a :=
    mul_le_mul_of_nonneg_right (by linarith) hRHS0
  nlinarith


lemma grad_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have h1 : Continuous (fun x => fderiv ℝ f x) := hf.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ (Vec n)).symm.continuous.comp h1

lemma pd_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (fun x => pd f x i) := by
  have := grad_continuous hf
  unfold pd
  fun_prop

lemma w_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) :
    Continuous (fun x => w f μ x) := by
  have := pd_continuous hf
  unfold w posPart
  fun_prop

lemma crit_of_w_zero {f : Vec n → ℝ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) {x : Vec n}
    (hx : x ∈ orthant n) (hw : w f μ x = 0) : IsCritical f x := by
  unfold w at hw
  rw [norm_eq_zero] at hw
  have hc : ∀ i, min (x i) (μ i * pd f x i) = 0 := by
    intro i
    have := congrArg (fun y : Vec n => y i) hw
    simp only [posPart, PiLp.sub_apply, PiLp.toLp_apply, PiLp.zero_apply] at this
    rw [← sub_max_eq_min]; exact this
  have hmain : ∀ i, 0 ≤ pd f x i ∧ (0 < x i → pd f x i = 0) := by
    intro i
    have h := hc i
    have hμi := hμ i
    rcases le_total (x i) (μ i * pd f x i) with h' | h'
    · rw [min_eq_left h'] at h
      refine ⟨?_, fun hp => absurd h (ne_of_gt hp)⟩
      by_contra hneg; push Not at hneg
      nlinarith
    · rw [min_eq_right h'] at h
      have : pd f x i = 0 := by
        rcases mul_eq_zero.1 h with h1 | h1
        · linarith
        · exact h1
      exact ⟨this.ge, fun _ => this⟩
  exact ⟨hx, fun i => (hmain i).1, fun i hi => (hmain i).2 hi⟩

lemma rhs_mono {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ}
    {x : Vec n} (hx : x ∈ orthant n) {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    armijoRHS f μ ε D x a ≤ armijoRHS f μ ε D x b := by
  unfold armijoRHS
  have hS := quad_nonneg hD hdiag (fun i => pd f x i)
  have hS' : 0 ≤ ∑ i ∈ (Ik f μ ε x)ᶜ, pd f x i * dir f D x i := hS
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right hab hS'
  · apply Finset.sum_le_sum
    intro i hi
    have hg := ((mem_Ik f μ ε x i).1 hi).2.2
    have hp := dir_pos_of_mem hD hdiag hi hg
    apply mul_le_mul_of_nonneg_left _ hg.le
    rw [arc_apply, arc_apply, sub_max_eq_min, sub_max_eq_min]
    apply min_le_min le_rfl
    nlinarith

lemma orthant_closed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {x : Vec n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [this]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by fun_prop)


/-- The continuous merit function used to pass to the limit. -/
noncomputable def Psi (f : Vec n → ℝ) (c : ℝ) (i : Fin n) (y : Vec n) : ℝ :=
  min (c * pd f y i ^ 2)
    (max 0 (pd f y i) * min (y i) (c * max 0 (pd f y i)) + min 0 (pd f y i) ^ 2)

lemma Psi_continuous {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) (c : ℝ) (i : Fin n) :
    Continuous (Psi f c i) := by
  have := pd_continuous hf i
  unfold Psi
  fun_prop

lemma Psi_nonneg {f : Vec n → ℝ} {c : ℝ} (hc : 0 ≤ c) (i : Fin n) {y : Vec n}
    (hy : y ∈ orthant n) : 0 ≤ Psi f c i y := by
  unfold Psi
  apply le_min (mul_nonneg hc (sq_nonneg _))
  have h1 : 0 ≤ max 0 (pd f y i) := le_max_left _ _
  have h2 : 0 ≤ min (y i) (c * max 0 (pd f y i)) := le_min (hy i) (mul_nonneg hc h1)
  nlinarith [sq_nonneg (min 0 (pd f y i))]

lemma crit_of_Psi {f : Vec n → ℝ} {c : ℝ} (hc : 0 < c) {y : Vec n} (hy : y ∈ orthant n)
    (h : ∀ i, Psi f c i y = 0) : IsCritical f y := by
  have hmain : ∀ i, 0 ≤ pd f y i ∧ (0 < y i → pd f y i = 0) := by
    intro i
    have hi := h i
    unfold Psi at hi
    set g := pd f y i
    rcases min_choice (c * g ^ 2) (max 0 g * min (y i) (c * max 0 g) + min 0 g ^ 2) with h' | h'
    · rw [h'] at hi
      have : g = 0 := by
        have : g ^ 2 = 0 := by
          rcases mul_eq_zero.1 hi with h1 | h1
          · linarith
          · exact h1
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      exact ⟨this.ge, fun _ => this⟩
    · rw [h'] at hi
      have h1 : 0 ≤ max 0 g := le_max_left _ _
      have h2 : 0 ≤ min (y i) (c * max 0 g) := le_min (hy i) (mul_nonneg hc.le h1)
      have h3 : 0 ≤ max 0 g * min (y i) (c * max 0 g) := mul_nonneg h1 h2
      have h4 : min 0 g ^ 2 = 0 := by nlinarith [sq_nonneg (min 0 g)]
      have hg0 : 0 ≤ g := by
        have : min 0 g = 0 := pow_eq_zero_iff two_ne_zero |>.1 h4
        rw [← this]; exact min_le_right _ _
      refine ⟨hg0, fun hyi => ?_⟩
      by_contra hne
      have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hne)
      rw [max_eq_right hgpos.le] at h3 hi
      have h5 : g * min (y i) (c * g) = 0 := by nlinarith
      have h6 : 0 < min (y i) (c * g) := lt_min hyi (mul_pos hc hgpos)
      have := mul_pos hgpos h6
      linarith
  exact ⟨hy, fun i => (hmain i).1, fun i hi => (hmain i).2 hi⟩

lemma Psi_le_rhs {f : Vec n → ℝ} {μ : Fin n → ℝ} {ε : ℝ} {x : Vec n} (hx : x ∈ orthant n)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hdiag : DiagonalWrt D (Ik f μ ε x))
    {c1 : ℝ} (hc1 : 0 < c1) (hlo : ∀ u : Fin n → ℝ, c1 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D *ᵥ u))
    {a : ℝ} (ha : 0 < a) (i : Fin n) :
    Psi f (a * c1) i x ≤ armijoRHS f μ ε D x a := by
  set I := Ik f μ ε x with hI
  set g : Fin n → ℝ := fun j => pd f x j with hg
  set gJ : Fin n → ℝ := fun j => if j ∈ I then 0 else g j
  have hS : ∑ j ∈ Iᶜ, pd f x j * dir f D x j = gJ ⬝ᵥ (D *ᵥ gJ) := by
    have := quad_eq hD.1 hdiag g
    simp only [star_trivial] at this
    exact this
  have hT : ∀ j ∈ I, 0 ≤ pd f x j * (x j - arc f D x a j) := by
    intro j hj
    have hgj := ((mem_Ik f μ ε x j).1 hj).2.2
    have hp := dir_pos_of_mem hD hdiag hj hgj
    apply mul_nonneg hgj.le
    rw [arc_apply, sub_max_eq_min]
    exact le_min (hx j) (by positivity)
  have hTs : 0 ≤ ∑ j ∈ I, pd f x j * (x j - arc f D x a j) := Finset.sum_nonneg hT
  have hSnn : 0 ≤ gJ ⬝ᵥ (D *ᵥ gJ) := posdef_nonneg hD gJ
  unfold armijoRHS
  rw [← hI, hS]
  by_cases hi : i ∈ I
  · have hgi := ((mem_Ik f μ ε x i).1 hi).2.2
    have hpi : dir f D x i = D i i * pd f x i := by
      simp only [dir]; rw [mulVec_diag hdiag _ hi]
    have hDii := diag_ge hlo i
    have hle : Psi f (a * c1) i x ≤ pd f x i * (x i - arc f D x a i) := by
      unfold Psi
      apply le_trans (min_le_right _ _)
      rw [max_eq_right hgi.le, min_eq_left hgi.le, arc_apply, sub_max_eq_min]
      have : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [this, add_zero]
      apply mul_le_mul_of_nonneg_left _ hgi.le
      apply min_le_min le_rfl
      rw [hpi]
      have := mul_le_mul_of_nonneg_right hDii hgi.le
      nlinarith
    have := Finset.single_le_sum hT hi
    nlinarith [mul_nonneg ha.le hSnn]
  · have hle : Psi f (a * c1) i x ≤ a * c1 * pd f x i ^ 2 := min_le_left _ _
    have h1 : pd f x i ^ 2 ≤ gJ ⬝ᵥ gJ := by
      have := Finset.single_le_sum (f := fun j => gJ j * gJ j) (fun j _ => mul_self_nonneg (gJ j))
        (Finset.mem_univ i)
      have h0 : gJ i = pd f x i := by simp only [gJ, if_neg hi, hg]
      rw [h0] at this
      rw [sq]; exact this
    have h2 := hlo gJ
    have h3 : a * c1 * pd f x i ^ 2 ≤ a * (gJ ⬝ᵥ (D *ᵥ gJ)) := by
      have := mul_le_mul_of_nonneg_left h1 hc1.le
      have := mul_le_mul_of_nonneg_left (le_trans this h2) ha.le
      nlinarith
    linarith


lemma prop2_core {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) (hA : AssumptionA f)
    (μ : Fin n → ℝ) (ε β σ : ℝ) (hpar : Params μ ε β σ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n)
    (hrun : IsRun f μ ε β σ D x)
    (hadm : AdmissibleScaling f μ ε D x)
    (lam1 lam2 : ℝ) (q₁ q₂ : ℕ)
    (hB : AssumptionB f μ D x lam1 lam2 q₁ q₂) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsCritical f xbar := by
  intro xbar hcl
  by_contra hnc
  have hμ := hpar.mu_pos
  have hε := hpar.eps_pos
  have hσ0 : 0 < σ := hpar.sigma_mem.1
  have hσ1 : σ < 1 / 2 := hpar.sigma_mem.2
  have hβ0 : 0 < β := hpar.beta_mem.1
  have hβ1 : β < 1 := hpar.beta_mem.2
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hstep := (wd_core hf μ ε β σ hpar).2 D x hrun hadm
  have hxo : ∀ k, x k ∈ orthant n := fun k => (hstep k).1
  have hanti : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    by_cases hc : IsCritical f (x k)
    · rw [(hstep k).2.2 hc]
    · exact ((hstep k).2.1 hc).le
  obtain ⟨ψ, hψ, hlim⟩ := hcl.tendsto_subseq
  have hxbo : xbar ∈ orthant n :=
    orthant_closed.mem_of_tendsto hlim (Eventually.of_forall (fun k => hxo _))
  set wb := w f μ xbar with hwb
  have hwbar : 0 < wb :=
    lt_of_le_of_ne (norm_nonneg _) (fun h => hnc (crit_of_w_zero hμ hxbo h.symm))
  set Gb := ‖gradient f xbar‖ + 1 with hGb
  have hGb1 : 1 ≤ Gb := by rw [hGb]; linarith [norm_nonneg (gradient f xbar)]
  -- eventual neighbourhood facts along the subsequence
  have hev1 : ∀ᶠ k in atTop, ‖x (ψ k) - xbar‖ ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.1 hlim 1 one_pos] with k hk
    rw [← dist_eq_norm]; exact hk.le
  have hwlim : Tendsto (fun k => w f μ (x (ψ k))) atTop (𝓝 wb) :=
    ((w_continuous hf μ).tendsto xbar).comp hlim
  have hev2 : ∀ᶠ k in atTop, wb / 2 ≤ w f μ (x (ψ k)) ∧ w f μ (x (ψ k)) ≤ wb + 1 := by
    filter_upwards [hwlim.eventually (Ioo_mem_nhds (by linarith : wb / 2 < wb)
      (by linarith : wb < wb + 1))] with k hk
    exact ⟨hk.1.le, hk.2.le⟩
  have hglim : Tendsto (fun k => ‖gradient f (x (ψ k))‖) atTop (𝓝 ‖gradient f xbar‖) :=
    ((continuous_norm.comp (grad_continuous hf)).tendsto xbar).comp hlim
  have hev3 : ∀ᶠ k in atTop, ‖gradient f (x (ψ k))‖ ≤ Gb := by
    filter_upwards [hglim.eventually (Iio_mem_nhds (by linarith : ‖gradient f xbar‖ < Gb))]
      with k hk
    exact hk.le
  -- constants
  obtain ⟨hl1, hl2, hBk⟩ := hB
  set c1 := lam1 * (wb / 2) ^ q₁ with hc1
  set c2 := lam2 * (wb + 1) ^ q₂ with hc2
  have hc1p : 0 < c1 := mul_pos hl1 (pow_pos (by linarith) _)
  have hc2p : 0 < c2 := mul_pos hl2 (pow_pos (by linarith) _)
  set εbar := min ε (wb / 2) with hεbar
  have hεbarp : 0 < εbar := lt_min hε (by linarith)
  obtain ⟨L, hL⟩ := hA (Metric.closedBall xbar (1 + c2 * Gb)) Metric.isBounded_closedBall
  have hL0 : (0:ℝ) ≤ L := L.2
  set abar := min 1 (min (εbar / (c2 * Gb)) ((1 - σ) / (L * c2 + 1))) with habar
  have hc2G : 0 < c2 * Gb := mul_pos hc2p (by linarith)
  have hLc : 0 < (L:ℝ) * c2 + 1 := by nlinarith
  have habarp : 0 < abar :=
    lt_min one_pos (lt_min (div_pos hεbarp hc2G) (div_pos (by linarith) hLc))
  have habar1 : abar ≤ 1 := min_le_left _ _
  have habarε : abar * (c2 * Gb) ≤ εbar := by
    have : abar ≤ εbar / (c2 * Gb) := le_trans (min_le_right _ _) (min_le_left _ _)
    rwa [le_div_iff₀ hc2G] at this
  have habarL : abar * (L * c2) ≤ 1 - σ := by
    have : abar ≤ (1 - σ) / (L * c2 + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    rw [le_div_iff₀ hLc] at this
    nlinarith
  -- per-index bounds
  have hbounds : ∀ᶠ k in atTop,
      (∀ u : Fin n → ℝ, c1 * (u ⬝ᵥ u) ≤ u ⬝ᵥ (D (ψ k) *ᵥ u)) ∧
      (∀ u : Fin n → ℝ, u ⬝ᵥ (D (ψ k) *ᵥ u) ≤ c2 * (u ⬝ᵥ u)) ∧
      εbar ≤ min ε (w f μ (x (ψ k))) ∧ ‖x (ψ k) - xbar‖ ≤ 1 ∧
      ‖gradient f (x (ψ k))‖ ≤ Gb := by
    filter_upwards [hev1, hev2, hev3] with k h1 h2 h3
    refine ⟨fun u => ?_, fun u => ?_, min_le_min le_rfl h2.1, h1, h3⟩
    · have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun j _ => mul_self_nonneg (u j))
      have := (hBk (ψ k) u).1
      have hp : (wb / 2) ^ q₁ ≤ w f μ (x (ψ k)) ^ q₁ :=
        pow_le_pow_left₀ (by linarith) h2.1 _
      have : c1 * (u ⬝ᵥ u) ≤ lam1 * w f μ (x (ψ k)) ^ q₁ * (u ⬝ᵥ u) := by
        apply mul_le_mul_of_nonneg_right _ huu
        exact mul_le_mul_of_nonneg_left hp hl1.le
      linarith
    · have huu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun j _ => mul_self_nonneg (u j))
      have := (hBk (ψ k) u).2
      have hw0 : 0 ≤ w f μ (x (ψ k)) := norm_nonneg _
      have hp : w f μ (x (ψ k)) ^ q₂ ≤ (wb + 1) ^ q₂ := pow_le_pow_left₀ hw0 h2.2 _
      have : lam2 * w f μ (x (ψ k)) ^ q₂ * (u ⬝ᵥ u) ≤ c2 * (u ⬝ᵥ u) := by
        apply mul_le_mul_of_nonneg_right _ huu
        exact mul_le_mul_of_nonneg_left hp hl2.le
      linarith
  -- stepsize lower bound and RHS control
  set a0 := β * abar with ha0
  have ha0p : 0 < a0 := mul_pos hβ0 habarp
  have hrhs : ∀ᶠ k in atTop,
      armijoRHS f μ ε (D (ψ k)) (x (ψ k)) a0 ≤ (f (x (ψ k)) - f (x (ψ k + 1))) / σ := by
    filter_upwards [hbounds] with k hk
    obtain ⟨hlo, hup, hεk, hxk, hGk⟩ := hk
    have harm : ∀ m : ℕ, β ^ m ≤ abar → Armijo f μ ε β σ (D (ψ k)) (x (ψ k)) m := by
      intro m hm
      unfold Armijo
      have hpos : 0 < β ^ m := pow_pos hβ0 m
      exact armijo_of_small hdiff hμ hε (by linarith) (hxo _) hxk (hadm (ψ k)).1
        (hadm (ψ k)).2 hc2p hup hGk hεk hL hpos (le_trans hm habar1)
        (le_trans (mul_le_mul_of_nonneg_right hm hc2G.le) habarε)
        (le_trans (mul_le_mul_of_nonneg_right hm (by positivity)) habarL)
    obtain ⟨m, hAm, hmin, hnext⟩ := hrun.2 (ψ k)
    have hm_ge : a0 ≤ β ^ m := by
      by_contra hlt
      push Not at hlt
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hlt
        have : β * abar < 1 := by nlinarith
        linarith
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      have : β ^ m' ≤ abar := by
        rw [pow_succ] at hlt
        have := (mul_lt_mul_iff_of_pos_right hβ0).1 (by linarith : β ^ m' * β < abar * β)
        exact this.le
      exact hmin m' (Nat.lt_succ_self m') (harm m' this)
    have hmono := rhs_mono (hxo (ψ k)) (hadm (ψ k)).1 (hadm (ψ k)).2 ha0p hm_ge
    unfold Armijo at hAm
    rw [← hnext] at hAm
    rw [le_div_iff₀ hσ0]
    nlinarith
  -- the function decrease along the subsequence tends to zero
  have hflim : Tendsto (fun k => f (x (ψ k))) atTop (𝓝 (f xbar)) :=
    ((hdiff.continuous).tendsto xbar).comp hlim
  have hfge : ∀ j, f xbar ≤ f (x j) := by
    intro j
    apply le_of_tendsto hflim
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hanti (le_trans hk (hψ.id_le k))
  have hdec : Tendsto (fun k => (f (x (ψ k)) - f (x (ψ k + 1))) / σ) atTop (𝓝 0) := by
    have hup : Tendsto (fun k => (f (x (ψ k)) - f xbar) / σ) atTop (𝓝 0) := by
      have := (hflim.sub_const (f xbar)).div_const σ
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    · intro k
      apply div_nonneg _ hσ0.le
      have := hanti (Nat.le_succ (ψ k))
      simp only at this
      linarith
    · intro k
      apply div_le_div_of_nonneg_right _ hσ0.le
      linarith [hfge (ψ k + 1)]
  -- pass to the limit in Psi
  have hcrit : ∀ i, Psi f (a0 * c1) i xbar = 0 := by
    intro i
    have hPlim : Tendsto (fun k => Psi f (a0 * c1) i (x (ψ k))) atTop
        (𝓝 (Psi f (a0 * c1) i xbar)) :=
      ((Psi_continuous hf (a0 * c1) i).tendsto xbar).comp hlim
    have hP0 : Tendsto (fun k => Psi f (a0 * c1) i (x (ψ k))) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdec
      · exact Eventually.of_forall (fun k => Psi_nonneg (mul_pos ha0p hc1p).le i (hxo _))
      · filter_upwards [hbounds, hrhs] with k hk hr
        exact le_trans (Psi_le_rhs (hxo _) (hadm (ψ k)).1 (hadm (ψ k)).2 hc1p hk.1 ha0p i) hr
    exact tendsto_nhds_unique hPlim hP0
  exact hnc (crit_of_Psi (mul_pos ha0p hc1p) hxbo hcrit)

end ProjNewton.Superlinear

open ProjNewton.Superlinear Matrix Filter Topology

theorem solution {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (hA : AssumptionA f)
    (μ : Fin n → ℝ) (ε β σ : ℝ) (hpar : Params μ ε β σ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n)
    (hrun : IsRun f μ ε β σ D x)
    (hadm : AdmissibleScaling f μ ε D x)
    (lam1 lam2 : ℝ) (q₁ q₂ : ℕ)
    (hB : AssumptionB f μ D x lam1 lam2 q₁ q₂) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsCritical f xbar :=
  prop2_core hf hA μ ε β σ hpar D x hrun hadm lam1 lam2 q₁ q₂ hB
