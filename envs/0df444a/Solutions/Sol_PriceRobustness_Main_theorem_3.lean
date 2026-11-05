-- Prove2me | solution 1 for PriceRobustness.Main.theorem_3
-- status  : ACCEPTED   (disprove)
-- author  : @frknbls
-- created : 2026-11-04T14:31:47.171613+00:00
-- url     : https://prove2.me/submissions/8b0b3ff1-2308-4ab9-a9a7-88385b49b2a4

import Definitions.Def_PriceRobustness_Main_RobustModel
import Definitions.Def_PriceRobustness_Main_Protection
import Definitions.Def_PriceRobustness_Main_Noise
import Definitions.Def_PriceRobustness_Main_Bounds

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
universe u

namespace PriceRobustness.Main.DisA

noncomputable def ρ : Measure (ULift.{u} ℝ) :=
  (1 / 2 : ENNReal) • (Measure.dirac (ULift.up 1) + Measure.dirac (ULift.up (-1)))

instance : IsProbabilityMeasure (ρ.{u}) := ⟨by
  simp only [ρ, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, one_div, ENNReal.inv_mul_cancel] <;> norm_num⟩

abbrev Ω := (↥(Finset.univ : Finset (Fin 4))) → ULift.{u} ℝ

noncomputable def P : Measure (Ω.{u}) := Measure.pi (fun _ => ρ.{u})

instance : IsProbabilityMeasure (P.{u}) := by unfold P; infer_instance

noncomputable def X : (↥(Finset.univ : Finset (Fin 4))) → ULift.{u} ℝ → ℝ :=
  fun j a => if j.val = 2 then max (-1) (min 1 a.down) else 0

noncomputable def η : Fin 4 → Ω.{u} → ℝ :=
  fun j ω => X ⟨j, Finset.mem_univ j⟩ (ω ⟨j, Finset.mem_univ j⟩)

noncomputable def D : RobustModel 1 4 where
  nominal := { A := fun _ _ => 0, b := fun _ => 100, c := fun _ => 0,
               lower := fun _ => 1, upper := fun _ => 1 }
  J := fun _ => Finset.univ
  radius := fun _ j => if j = 3 then 1 / 10 else 1
  budget := fun _ => 2
  radius_nonneg := by intro i j _; split_ifs <;> norm_num
  budget_mem := by intro i; simp; norm_num

end PriceRobustness.Main.DisA

open PriceRobustness.Main PriceRobustness.Main.DisA in
theorem _root_.solution : ¬ (
    (∀ (m N : ℕ) (D : RobustModel m N) (x : Fin N → ℝ), D.Optimal x →
      ∀ (i : Fin m) (S : Finset (Fin N)) (t r : Option (Fin N)),
      MaximizesProtection (D.J i) (D.weight x i) (D.budget i) S t →
      MinimizesSelected (D.weight x i) S t r → 1 ≤ D.budget i →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Fin N → Ω → ℝ), SymmetricNoise P (D.J i) η →
      P.real {ω | (∑ j ∈ D.J i, sourceGamma (D.weight x i) S r j * η j ω) ≥
        D.budget i} ≤ B (D.J i).card (D.budget i)) ∧
    (∀ (n g : ℕ), 1 ≤ g → g ≤ n → Even (g + n) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Fin n → Ω → ℝ),
      (∀ j, Measurable (η j)) → iIndepFun η P →
      (∀ j, P.real {ω | η j ω = 1} = 1 / 2 ∧
        P.real {ω | η j ω = -1} = 1 / 2) →
      P.real {ω | (∑ j, η j ω) ≥ (g : ℝ)} = B n g) ∧
    (∀ (n : ℕ) (Γ : ℝ), 1 ≤ Γ → Γ ≤ (n : ℝ) →
      B n Γ ≤ (1 - mu n Γ) * C n ⌊nu n Γ⌋ +
        ∑ l ∈ (Finset.range (n + 1)).filter (fun l : ℕ => ⌊nu n Γ⌋ + 1 ≤ (l : ℤ)),
          C n l) ∧
    (∀ θ : ℝ, Tendsto (fun n : ℕ => B n (θ * Real.sqrt n)) atTop
      (𝓝 (1 - Phi θ)))) := by
  intro h
  have hw : ∀ j, D.weight (fun _ => 1) 0 j = if j = 3 then 1 / 10 else 1 := by
    intro j; simp [RobustModel.weight, D]
  have hopt : D.Optimal (fun _ => 1) := by
    refine ⟨⟨fun _ => 1, fun _ => 0, fun i j => D.radius i j * 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro i; simp [D, Fin.sum_univ_four]; norm_num
    · intro i j _; simp
    · intro j; norm_num
    · intro j; simp [D]
    · intro i j _; simp [D]; split_ifs <;> norm_num
    · intro j; norm_num
    · intro i; norm_num
    · intro x' y z p _; simp [D, LinearProgram.objective]
  have hmax : MaximizesProtection (D.J 0) (D.weight (fun _ => 1) 0) (D.budget 0)
      {0, 1} (some 3) := by
    have hadm : AdmissibleProtection (D.J 0) {0, 1} (D.budget 0) (some 3) := by
      refine ⟨by simp [D], by simp [D]; norm_num, ?_⟩
      rw [if_neg (by simp [D])]
      refine ⟨by simp [D], by simp [D], 3, by simp [D], by decide, rfl⟩
    refine ⟨hadm, ?_⟩
    intro S' t' h'
    obtain ⟨-, -, h3⟩ := h'
    rw [if_neg (by simp [D])] at h3
    obtain ⟨-, hc, -⟩ := h3
    have hfl : ⌊D.budget 0⌋ = 2 := by simp [D]
    simp only [protectionValue, hfl]
    have : D.budget 0 = 2 := rfl
    rw [this]
    have hc' : S'.card = 2 := by rw [hfl] at hc; exact_mod_cast hc
    have hle : ∑ j ∈ S', D.weight (fun _ => 1) 0 j ≤ S'.card • (1 : ℝ) := by
      apply Finset.sum_le_card_nsmul
      intro j _; rw [hw]; split_ifs <;> norm_num
    rw [hc'] at hle
    have hS : ∑ j ∈ ({0, 1} : Finset (Fin 4)), D.weight (fun _ => 1) 0 j = 2 := by
      rw [Finset.sum_pair (by decide), hw, hw, if_neg (by decide), if_neg (by decide)]; norm_num
    rw [hS]; push_cast; norm_num at hle ⊢; linarith
  have hmin : MinimizesSelected (D.weight (fun _ => 1) 0) {0, 1} (some 3) (some 3) := by
    refine ⟨3, rfl, by decide, ?_⟩
    intro l _; rw [hw, hw]; split_ifs <;> simp_all <;> norm_num
  have hb1 : (1 : ℝ) ≤ D.budget 0 := by simp [D]
  -- the noise
  have i2mem : (2 : Fin 4) ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ _
  set i2 : (↥(Finset.univ : Finset (Fin 4))) := ⟨2, i2mem⟩ with hi2
  have hcm : Measurable (fun a : ULift.{0} ℝ => max (-1) (min 1 a.down)) :=
    measurable_const.max (measurable_const.min measurable_down)
  have hη2 : η.{0} 2 = fun ω => max (-1) (min 1 (ω i2).down) := by
    funext ω; simp [η, X]; rfl
  have hηo : ∀ j : Fin 4, j ≠ 2 → η.{0} j = fun _ => 0 := by
    intro j hj; funext ω; simp [η, X, hj]
  have hmapP : (P.{0}).map (fun ω : Ω.{0} => ω i2) = ρ.{0} :=
    (measurePreserving_eval (fun _ => ρ.{0}) i2).map_eq
  have hev : Measurable (fun ω : Ω.{0} => ω i2) := measurable_pi_apply i2
  have hlaw : (P.{0}).map (η 2) = (1 / 2 : ENNReal) • (Measure.dirac 1 + Measure.dirac (-1)) := by
    rw [hη2, show (fun ω : Ω.{0} => max (-1) (min 1 (ω i2).down)) =
      (fun a : ULift.{0} ℝ => max (-1) (min 1 a.down)) ∘ (fun ω : Ω.{0} => ω i2) from rfl,
      ← Measure.map_map hcm hev, hmapP, ρ, Measure.map_smul, Measure.map_add _ _ hcm,
      Measure.map_dirac' hcm, Measure.map_dirac' hcm]
    norm_num
  have hlawn : (P.{0}).map (fun ω => - η 2 ω) =
      (1 / 2 : ENNReal) • (Measure.dirac 1 + Measure.dirac (-1)) := by
    have hcm' : Measurable (fun a : ULift.{0} ℝ => -max (-1) (min 1 a.down)) := hcm.neg
    rw [hη2, show (fun ω : Ω.{0} => -max (-1) (min 1 (ω i2).down)) =
      (fun a : ULift.{0} ℝ => -max (-1) (min 1 a.down)) ∘ (fun ω : Ω.{0} => ω i2) from rfl,
      ← Measure.map_map hcm' hev, hmapP, ρ, Measure.map_smul, Measure.map_add _ _ hcm',
      Measure.map_dirac' hcm', Measure.map_dirac' hcm']
    norm_num [add_comm]
  have hsym : SymmetricNoise P.{0} (D.J 0) η.{0} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j _
      by_cases hj : j = 2
      · subst hj; rw [hη2]; exact hcm.comp hev
      · rw [hηo j hj]; exact measurable_const
    · intro j _ ω
      by_cases hj : j = 2
      · subst hj; rw [hη2]
        exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
      · rw [hηo j hj]; simp
    · intro j _
      by_cases hj : j = 2
      · subst hj
        refine ⟨?_, ?_, ?_⟩
        · rw [hη2]; exact (hcm.comp hev).aemeasurable
        · rw [hη2]; exact (hcm.comp hev).neg.aemeasurable
        · rw [hlaw, hlawn]
      · rw [hηo j hj]; simp only [neg_zero]; exact IdentDistrib.refl aemeasurable_const
    · exact iIndepFun_pi (μ := fun _ => ρ.{0}) (X := X) (fun j => by
        unfold X; split_ifs
        · exact hcm.aemeasurable
        · exact aemeasurable_const)
  have key := h.1 1 4 D (fun _ => 1) hopt 0 {0, 1} (some 3) (some 3) hmax hmin hb1
    Ω.{0} P.{0} η.{0} hsym
  have hset : {ω | (∑ j ∈ D.J 0, sourceGamma (D.weight (fun _ => 1) 0) {0, 1} (some 3) j * η j ω)
      ≥ D.budget 0} = η.{0} 2 ⁻¹' {x | 2 ≤ 10 * x} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have : D.J 0 = Finset.univ := rfl
    rw [this, Fin.sum_univ_four, hηo 0 (by decide), hηo 1 (by decide), hηo 3 (by decide)]
    have hg : sourceGamma (D.weight (fun _ => 1) 0) {0, 1} (some 3) 2 = 10 := by
      simp only [sourceGamma, Option.elim, hw]
      rw [if_neg (by decide), if_neg (by decide)]; norm_num
    rw [hg]; simp [D]
  have hmeas2 : Measurable (η.{0} 2) := by rw [hη2]; exact hcm.comp hev
  have hL : P.{0}.real {ω | (∑ j ∈ D.J 0, sourceGamma (D.weight (fun _ => 1) 0) {0, 1} (some 3) j
      * η j ω) ≥ D.budget 0} = 1 / 2 := by
    rw [hset, measureReal_def, ← Measure.map_apply hmeas2 (measurableSet_le measurable_const
      (measurable_id.const_mul 10) : MeasurableSet {x : ℝ | 2 ≤ 10 * x}), hlaw]
    simp [Measure.smul_apply, Measure.add_apply]
    norm_num
  have hB : B (D.J 0).card (D.budget 0) = 5 / 16 := by
    have h1 : (D.J 0).card = 4 := rfl
    have h2 : D.budget 0 = 2 := rfl
    rw [h1, h2]
    simp only [B, mu, nu, binomialTail]
    norm_num
    rw [Finset.sum_filter, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.choose]
  rw [hL, hB] at key
  norm_num at key
