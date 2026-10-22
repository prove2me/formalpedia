-- Prove2me | solution 1 for ShapeMoment.LogConcave.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:40:28.038997+00:00
-- url     : https://prove2.me/submissions/6a40f518-38f3-42ab-9f1c-84c4296f5bb8

import Theorems.Thm_ShapeMoment_LogConcave_theorem_3_1
import Definitions.Def_ShapeMoment_LogConcave_ReverseConvex

open ShapeMoment.LogConcave

theorem isOpen_forall_pos_of_pos {n : ℕ} (x : Fin n → ℝ) :
    IsOpen {y : Fin n → ℝ | ∀ j, 0 < x j → 0 < y j} := by
  have : {y : Fin n → ℝ | ∀ j, 0 < x j → 0 < y j} = ⋂ j, {y | 0 < x j → 0 < y j} := by
    ext; simp
  rw [this]
  refine isOpen_iInter_of_finite fun j => ?_
  by_cases hj : 0 < x j
  · simpa [hj] using isOpen_lt continuous_const (continuous_apply j)
  · simp [hj]

theorem ext_tight_aux {n m P : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (f : Fin P → (Fin n → ℝ) → ℝ) (hcont : ∀ p, Continuous (f p))
    (hrc : ∀ p, Convex ℝ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x})
    (x : Fin n → ℝ) (hx : x ∈ (revCvxFeasible A b f).extremePoints ℝ) :
    n - m ≤ (Finset.univ.filter (fun p : Fin P => f p x = 0)).card +
        (Finset.univ.filter (fun j : Fin n => x j = 0)).card := by
  classical
  obtain ⟨⟨hx0, hAx, hfx⟩, hext⟩ := hx
  by_contra hlt
  push Not at hlt
  have hT : Fintype.card {p : Fin P // f p x = 0} =
      (Finset.univ.filter (fun p : Fin P => f p x = 0)).card := Fintype.card_subtype _
  have hZ : Fintype.card {j : Fin n // x j = 0} =
      (Finset.univ.filter (fun j : Fin n => x j = 0)).card := Fintype.card_subtype _
  let Φ : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) × ({j : Fin n // x j = 0} → ℝ) :=
    LinearMap.prod (Matrix.mulVecLin A)
      (LinearMap.pi fun j : {j : Fin n // x j = 0} => LinearMap.proj (j : Fin n))
  let W := LinearMap.ker Φ
  have hWZ : ∀ w : W, ∀ j, x j = 0 → (w : Fin n → ℝ) j = 0 := by
    intro w j hj
    have h := w.2
    rw [LinearMap.mem_ker] at h
    exact congrFun (congrArg Prod.snd h) ⟨j, hj⟩
  have hWA : ∀ w : W, A.mulVec (w : Fin n → ℝ) = 0 := by
    intro w
    have h := w.2
    rw [LinearMap.mem_ker] at h
    exact congrArg Prod.fst h
  have hW : Fintype.card {p : Fin P // f p x = 0} < Module.finrank ℝ W := by
    have h1 := Φ.finrank_range_add_finrank_ker
    have h2 : Module.finrank ℝ (LinearMap.range Φ) ≤ m + Fintype.card {j : Fin n // x j = 0} := by
      calc _ ≤ Module.finrank ℝ ((Fin m → ℝ) × ({j : Fin n // x j = 0} → ℝ)) :=
            Submodule.finrank_le _
        _ = m + Fintype.card {j : Fin n // x j = 0} := by
            simp [Module.finrank_prod]
    simp only [Module.finrank_fin_fun] at h1
    have h3 : Module.finrank ℝ W = Module.finrank ℝ (LinearMap.ker Φ) := rfl
    omega
  have hsep : ∀ p : {p : Fin P // f p x = 0}, ∃ φ : StrongDual ℝ W, ∀ w : W,
      (∀ j, 0 < x j → 0 < (x + (w : Fin n → ℝ)) j) → 0 < f p (x + w) → 0 < φ w := by
    intro p
    let C : Set W := {w | (∀ j, 0 < x j → 0 < (x + (w : Fin n → ℝ)) j) ∧ 0 < f p (x + w)}
    have hCconv : Convex ℝ C := by
      intro w1 h1 w2 h2 a c ha hc hac
      have hmem : ∀ w : W, w ∈ C →
          x + (w : Fin n → ℝ) ∈ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x} := by
        intro w hw
        refine ⟨fun j => ?_, hw.2⟩
        rcases (hx0 j).lt_or_eq with hj | hj
        · exact (hw.1 j hj).le
        · simp [← hj, hWZ w j hj.symm]
      have hcomb := hrc p (hmem w1 h1) (hmem w2 h2) ha hc hac
      have heq : a • (x + (w1 : Fin n → ℝ)) + c • (x + (w2 : Fin n → ℝ)) =
          x + ((a • w1 + c • w2 : W) : Fin n → ℝ) := by
        ext j; simp; linear_combination (x j) * hac
      rw [heq] at hcomb
      refine ⟨fun j hj => ?_, hcomb.2⟩
      have e1 := h1.1 j hj
      have e2 := h2.1 j hj
      simp only [Pi.add_apply, Submodule.coe_add, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul] at e1 e2 ⊢
      have : x j + (a * (w1 : Fin n → ℝ) j + c * (w2 : Fin n → ℝ) j) =
          a * (x j + (w1 : Fin n → ℝ) j) + c * (x j + (w2 : Fin n → ℝ) j) := by
        linear_combination (-(x j)) * hac
      rw [this]
      rcases ha.lt_or_eq with ha' | ha'
      · have := mul_pos ha' e1
        have := mul_nonneg hc e2.le
        linarith
      · subst ha'
        have hc1 : c = 1 := by linarith
        subst hc1
        simpa using e2
    have hCopen : IsOpen C := by
      have hcf : Continuous fun w : W => x + (w : Fin n → ℝ) :=
        continuous_const.add continuous_subtype_val
      have hV : IsOpen {y : Fin n → ℝ | (∀ j, 0 < x j → 0 < y j) ∧ 0 < f p y} :=
        (isOpen_forall_pos_of_pos x).inter (isOpen_lt continuous_const (hcont p))
      exact hV.preimage hcf
    have h0 : (0 : W) ∉ C := by
      rintro ⟨-, h⟩
      simp [p.2] at h
    obtain ⟨φ, hφ⟩ := geometric_hahn_banach_point_open hCconv hCopen h0
    exact ⟨φ, fun w h1 h2 => by simpa using hφ w ⟨h1, h2⟩⟩
  choose φ hφ using hsep
  let Ψ : W →ₗ[ℝ] ({p : Fin P // f p x = 0} → ℝ) :=
    LinearMap.pi fun p => (φ p : W →ₗ[ℝ] ℝ)
  have hker : LinearMap.ker Ψ ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hW)
  obtain ⟨w, hwk, hw0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hφw : ∀ p, φ p w = 0 := fun p => congrFun hwk p
  set d : Fin n → ℝ := (w : Fin n → ℝ) with hd
  have hd0 : d ≠ 0 := fun h => hw0 (Subtype.ext h)
  let U : Set (Fin n → ℝ) := {y | (∀ j, 0 < x j → 0 < y j) ∧ ∀ p, f p x < 0 → f p y < 0}
  have hU : IsOpen U := by
    refine (isOpen_forall_pos_of_pos x).inter ?_
    have : {y : Fin n → ℝ | ∀ p, f p x < 0 → f p y < 0} = ⋂ p, {y | f p x < 0 → f p y < 0} := by
      ext; simp
    show IsOpen {y : Fin n → ℝ | ∀ p, f p x < 0 → f p y < 0}
    rw [this]
    refine isOpen_iInter_of_finite fun p => ?_
    by_cases hp : f p x < 0
    · simpa [hp] using isOpen_lt (hcont p) continuous_const
    · simp [hp]
  have hxU : x ∈ U := ⟨fun j h => h, fun p h => h⟩
  have hev : ∀ᶠ t in nhds (0:ℝ), x + t • d ∈ U := by
    have hcontl : Continuous fun t : ℝ => x + t • d :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact hcontl.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hxU))
  obtain ⟨ε, hε, hεU⟩ := Metric.eventually_nhds_iff.mp hev
  have hfeas : ∀ t : ℝ, x + t • d ∈ U → x + t • d ∈ revCvxFeasible A b f := by
    rintro t ⟨hpos, hneg⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rcases (hx0 j).lt_or_eq with hj | hj
      · exact (hpos j hj).le
      · simp [← hj, hd, hWZ w j hj.symm]
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hd, hWA w, smul_zero, add_zero, hAx]
    · intro p
      by_cases hp : f p x = 0
      · by_contra hgt
        push Not at hgt
        have := hφ ⟨p, hp⟩ (t • w)
          (by intro j hj; simpa [hd] using hpos j hj) (by simpa [hd] using hgt)
        rw [map_smul, hφw, smul_zero] at this
        exact lt_irrefl _ this
      · exact (hneg p (lt_of_le_of_ne (hfx p) hp)).le
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  have h1 := hfeas (ε/2) (hεU (by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hε2]; linarith))
  have h2 := hfeas (-(ε/2)) (hεU (by
    rw [dist_zero_right, norm_neg, Real.norm_eq_abs, abs_of_pos hε2]; linarith))
  have hseg : x ∈ openSegment ℝ (x + (ε/2) • d) (x + (-(ε/2)) • d) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j; simp; ring
  have key := hext h1 h2 hseg
  apply hd0
  have heq : x + (ε/2) • d = x := key
  have : (ε/2) • d = 0 := by
    have := congrArg (fun y => y - x) heq
    simpa using this
  exact (smul_eq_zero.mp this).resolve_left hε2.ne'

theorem solution (n m P : ℕ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : (Fin n → ℝ) → ℝ)
    (f : Fin P → (Fin n → ℝ) → ℝ)
    (hc : Continuous c) (hqc : QuasiconcaveOn ℝ Set.univ c)
    (hrank : A.rank = m) (hfdiff : ∀ p, Differentiable ℝ (f p))
    (hrc : ∀ p, Convex ℝ {x : Fin n → ℝ | (∀ j, 0 ≤ x j) ∧ 0 < f p x})
    (hne : (revCvxFeasible A b f).Nonempty)
    (hcompact : IsCompact (revCvxFeasible A b f)) :
    (∃ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x) ∧
    ∀ x ∈ (revCvxFeasible A b f).extremePoints ℝ,
      IsMinOn c (revCvxFeasible A b f) x →
      n - m ≤ (Finset.univ.filter (fun p : Fin P => f p x = 0)).card +
        (Finset.univ.filter (fun j : Fin n => x j = 0)).card := by
  refine ⟨theorem_3_1 n _ c hne hcompact hc.lowerSemicontinuous hqc, ?_⟩
  intro x hx _
  exact ext_tight_aux A b f (fun p => (hfdiff p).continuous) hrc x hx
