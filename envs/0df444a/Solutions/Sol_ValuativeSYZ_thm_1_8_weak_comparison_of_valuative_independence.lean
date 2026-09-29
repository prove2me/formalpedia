-- Prove2me | solution 1 for ValuativeSYZ.thm_1_8_weak_comparison_of_valuative_independence
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T13:33:21.553556+00:00
-- url     : https://prove2.me/submissions/ac362ef3-c3cb-4c94-bb12-7e56e55eed2f

import Mathlib
import Definitions.Def_ValuativeSYZ_cost_transform
import Definitions.Def_ValuativeSYZ_degeneration

/-! Disproof of da1be9b1 `ValuativeSYZ.thm_1_8_weak_comparison_of_valuative_independence`.

The `Degeneration` interface never ties the valuation of a section at an arbitrary point
`x` of the Berkovich space to its valuation at `emb (retract x)`, so nothing forces a
potential to factor through the retraction. Counterexample at `N = n = 0`: `Berk = Bool`,
`K = ℝ`, `Sect l = ℝ`, faces `= skFaces = {{0}}`, `Sk = {0}` (`μH[0] {0} = 1`),
`retract ≡ 0`, `emb ≡ true`, `valK ≡ 0`, `val x s = -(l * f x)` with `f true = 0`,
`f false = 1`. Then FS = CPSH = `{f + c}`, `MA ≡ dirac true = mu0`, every field holds,
the 1-element basis of each `Sect l` is valuatively independent and `f` is an NA CY potential.
Weak comparison would need an open `U ∋ 0` (else `mu0 (emb '' (U ∩ Sk)) = 0`), and then
`retract false = 0 ∈ U ∩ Sk` forces `f false = f true`, i.e. `1 = 0`. -/

set_option autoImplicit false

/-- The potential on the two-point Berkovich space `Bool`: `0` at `true`, `1` at `false`. -/
def fDa1b (b : Bool) : ℝ := if b then 0 else 1

open MeasureTheory ValuativeSYZ in
noncomputable def degDa1b : Degeneration Bool ℝ (fun _ => ℝ) 0 0 where
  faces := {{0}}
  faces_convex := by
    intro F hF
    rw [Finset.mem_singleton] at hF
    subst hF
    exact convex_singleton 0
  faces_compact := by
    intro F hF
    rw [Finset.mem_singleton] at hF
    subst hF
    exact isCompact_singleton
  skFaces := {{0}}
  skFaces_subset := Finset.Subset.refl _
  Sk := {0}
  Sk_eq := by simp
  Sk_hausdorff_pos := by
    rw [Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
    exact one_pos
  Sk_hausdorff_lt_top := by
    rw [Nat.cast_zero, Measure.hausdorffMeasure_zero_singleton]
    exact ENNReal.one_lt_top
  retract := fun _ => 0
  emb := fun _ => true
  emb_measurable := measurable_const
  retract_emb := by
    intro x hx
    simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Set.mem_singleton_iff] at hx
    exact hx.symm
  valK := fun _ => 0
  valK_mul := by intros; simp
  mulSect := fun {l l'} s s' => ((s : ℝ) * (s' : ℝ) : ℝ)
  val := fun {l} x _ => -((l : ℝ) * fDa1b x)
  val_smul := by intros; simp
  val_mul := by intros; push_cast; ring
  val_lipschitz := by
    refine ⟨0, ?_⟩
    intro l s F x y _ _ hF hx hy
    rw [Finset.mem_singleton] at hF
    subst hF
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp
  FS := {φ | ∃ c : ℝ, ∀ x, φ x = fDa1b x + c}
  FS_eq := by
    intro φ
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨1, 1, fun _ => (1 : ℝ), fun _ => -c, one_pos, one_pos, fun _ => one_ne_zero, ?_⟩
      intro x
      simp [hc x]
    · rintro ⟨l, m, s, cst, hm, hl, -, h⟩
      have hl' : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
      have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)
      refine ⟨(l : ℝ)⁻¹ * Finset.univ.sup' hne (fun i => -cst i), ?_⟩
      intro x
      rw [h x]
      have key : (Finset.univ.sup' hne fun i => (-(-((l : ℝ) * fDa1b x)) - cst i)) =
          (l : ℝ) * fDa1b x + Finset.univ.sup' hne (fun i => -cst i) := by
        rw [Finset.add_sup']
        congr 1
        funext i
        ring
      rw [key]
      field_simp
  CPSH := {φ | ∃ c : ℝ, ∀ x, φ x = fDa1b x + c}
  CPSH_eq := by
    intro φ
    constructor
    · intro hφ
      refine ⟨fun _ => φ, fun _ => hφ, ?_⟩
      intro u hu
      exact Filter.Eventually.of_forall fun _ _ => refl_mem_uniformity hu
    · rintro ⟨ψ, hψ, hconv⟩
      choose c hc using hψ
      refine ⟨φ true - fDa1b true, ?_⟩
      have ht := hconv.tendsto_at true
      have hf := hconv.tendsto_at false
      have ht' : Filter.Tendsto c Filter.atTop (nhds (φ true - fDa1b true)) := by
        have := ht.sub_const (fDa1b true)
        refine this.congr ?_
        intro k
        rw [hc k true]
        ring
      have hf' : Filter.Tendsto c Filter.atTop (nhds (φ false - fDa1b false)) := by
        have := hf.sub_const (fDa1b false)
        refine this.congr ?_
        intro k
        rw [hc k false]
        ring
      have heq := tendsto_nhds_unique ht' hf'
      intro x
      cases x
      · linarith
      · ring
  cpsh_convex := by
    intro φ _ F hF
    rw [Finset.mem_singleton] at hF
    subst hF
    refine ⟨convex_singleton 0, ?_⟩
    intro x hx y hy a b _ _ hab
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp only [smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  cpsh_lipschitz := by
    refine ⟨0, ?_⟩
    intro φ _ F hF x hx y hy
    rw [Finset.mem_singleton] at hF
    subst hF
    rw [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp
  deg := 1
  deg_pos := one_pos
  MA := fun _ => Measure.dirac true
  MA_total := by
    intro φ _
    simp
  MA_exists := by
    intro μ hμ hsupp
    refine ⟨fDa1b, ⟨0, fun x => (add_zero _).symm⟩, ?_⟩
    have himg : ((fun _ : EuclideanSpace ℝ (Fin 0) => true) ''
        ⋃ F ∈ ({{0}} : Finset (Set (EuclideanSpace ℝ (Fin 0)))), F) = {true} := by
      simp
    rw [himg] at hsupp
    have h1 : μ {true} = 1 := (prob_compl_eq_zero_iff (measurableSet_singleton true)).mp hsupp
    have hae : ∀ᵐ a ∂μ, a ∈ ({true} : Set Bool) := by
      rw [ae_iff]
      exact hsupp
    have hres : μ.restrict {true} = μ := Measure.restrict_eq_self_of_ae_mem hae
    conv_rhs => rw [← hres]
    rw [Measure.restrict_singleton, h1, ENNReal.ofReal_one, one_smul, one_smul]
  MA_unique := by
    rintro φ ⟨a, ha⟩ ψ ⟨b, hb⟩ -
    refine ⟨a - b, fun x => ?_⟩
    rw [ha x, hb x]
    ring
  MA_domination := by
    rintro φ ⟨a, ha⟩ ψ ⟨b, hb⟩ - hae x
    rw [ae_dirac_iff (MeasurableSet.of_discrete)] at hae
    rw [ha true, hb true] at hae
    rw [ha x, hb x]
    linarith

open MeasureTheory ValuativeSYZ in
theorem solution : ¬ (∀ {Berk : Type} [MeasurableSpace Berk] {K : Type} [Field K]
    {Sect : ℕ → Type} [∀ l, AddCommGroup (Sect l)] [∀ l, Module K (Sect l)] {N n : ℕ}
    (D : Degeneration Berk K Sect N n)
    (hVI : ∀ l : ℕ, ∃ (m : ℕ) (θ : Module.Basis (Fin m) K (Sect l)),
      D.ValuativeIndependent l θ)
    (φ₀ : Berk → ℝ) (hφ₀ : D.IsNACYPotential φ₀),
    D.WeakComparisonProperty φ₀) := by
  intro H
  have hVI : ∀ l : ℕ, ∃ (m : ℕ) (θ : Module.Basis (Fin m) ℝ ((fun _ : ℕ => ℝ) l)),
      degDa1b.ValuativeIndependent l θ := by
    intro l
    refine ⟨1, Module.Basis.singleton (Fin 1) ℝ, ?_⟩
    intro x _ a hne
    simp [degDa1b]
  have hmu0 : degDa1b.mu0 = Measure.dirac true := by
    show Measure.map (fun _ : EuclideanSpace ℝ (Fin 0) => true)
      ((μH[((0 : ℕ) : ℝ)] ({0} : Set (EuclideanSpace ℝ (Fin 0))))⁻¹ •
        (μH[((0 : ℕ) : ℝ)]).restrict ({0} : Set (EuclideanSpace ℝ (Fin 0)))) = Measure.dirac true
    rw [Measure.map_const]
    simp [Measure.hausdorffMeasure_zero_singleton]
  have hφ₀ : degDa1b.IsNACYPotential fDa1b := by
    refine ⟨⟨0, fun x => (add_zero _).symm⟩, ?_⟩
    rw [hmu0]
    simp [degDa1b]
  obtain ⟨U, _, hU1, hU⟩ := H degDa1b hVI fDa1b hφ₀
  have h0U : (0 : EuclideanSpace ℝ (Fin 0)) ∈ U := by
    by_contra h0
    have hempty : U ∩ degDa1b.Sk = ∅ := by
      ext y
      simp only [degDa1b, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hy hy0
      exact h0 (hy0 ▸ hy)
    rw [hempty, Set.image_empty, measure_empty] at hU1
    exact zero_ne_one hU1
  have hx := hU false (by simp [degDa1b, h0U])
  simp [degDa1b, fDa1b] at hx
