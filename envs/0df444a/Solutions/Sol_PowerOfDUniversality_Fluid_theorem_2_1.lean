-- Prove2me | solution 1 for PowerOfDUniversality.Fluid.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T02:00:51.495967+00:00
-- url     : https://prove2.me/submissions/a2572acd-ad6c-47f5-bbb2-aebf10dcef41
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PowerOfDUniversality_Fluid_Model
import Definitions.Def_PowerOfDUniversality_Fluid_FluidSpace
import Definitions.Def_PowerOfDUniversality_Fluid_Universality
import Theorems.Thm_PowerOfDUniversality_Fluid_proposition_4_9
import Theorems.Thm_PowerOfDUniversality_Fluid_theorem_4_1
import Theorems.Thm_PowerOfDUniversality_Fluid_theorem_4_1_lam_zero

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace PowerOfDUniversality.Fluid.Thm21Aux

open PowerOfDUniversality.Fluid

/-- Theorem 4.1 (both `λ > 0` and the boundary case `λ = 0`) in the form used by
Proposition 4.9: deterministic initial states converging in `ℓ¹`. -/
lemma jsqFluidLimit_of (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam0 : 0 ≤ lam) :
    JSQFluidLimit b lam := by
  intro Ns lamN Q0 qinf Ω _ P _ sys h1 h2 h3 h4 hq hsys hconv
  have hinit : ∀ ε : ℝ, 0 < ε → Tendsto (fun j => P {ω | ENNReal.ofReal ε ≤
      l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf}) atTop (𝓝 0) := by
    intro ε hε
    have hev : ∀ᶠ j in atTop, l1dist (scaledOcc (Ns j) (Q0 j)) qinf < ENNReal.ofReal ε :=
      hconv.eventually (gt_mem_nhds (by simpa using hε))
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with j hj
    have : {ω : Ω | ENNReal.ofReal ε ≤ l1dist (scaledOcc (Ns j) ((sys j).Q0 ω)) qinf} = ∅ := by
      ext ω
      simp only [hsys, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact hj
    rw [this, measure_empty]
  rcases hlam0.lt_or_eq with hpos | hzero
  · exact theorem_4_1 b hb lam hpos Ns h1 h2 lamN h3 h4 qinf hq P sys hinit
  · subst hzero
    exact theorem_4_1_lam_zero b hb Ns h1 h2 lamN h3 h4 qinf hq P sys hinit

/-- `SubseqFluidLimit` transfers along a measurable map: laws are computed through the
pushforward measure. -/
lemma subseq_transfer {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] (P : Measure Ω)
    (Φ : Ω → Ω₀) (hΦ : Measurable Φ) (b : ℕ∞) (lam : ℝ) (qinf : ℕ → ℝ)
    (Z' : ℕ → Ω₀ → ℝ → ℕ → ℝ) (h : SubseqFluidLimit (P.map Φ) b lam qinf Z') :
    SubseqFluidLimit P b lam qinf (fun j ω t => Z' j (Φ ω) t) := by
  intro φ hφ
  obtain ⟨ψ, hψ, Ω', mΩ', P', q, hP', hq, hconv⟩ := h φ hφ
  refine ⟨ψ, hψ, Ω', mΩ', P', q, hP', hq, ?_⟩
  obtain ⟨Ω'', m'', P'', Y, Ylim, hP'', hY, hYlim, hcad, hae⟩ := hconv
  refine ⟨Ω'', m'', P'', Y, Ylim, hP'', ?_, hYlim, hcad, hae⟩
  filter_upwards [hY] with n hn
  refine hn.trans ?_
  have hf := hn.aemeasurable_snd
  exact ⟨hf, hf.comp_measurable hΦ, AEMeasurable.map_map_of_aemeasurable hf hΦ.aemeasurable⟩

/-- The joint path of all clocks and marks. -/
def joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {b : ℕ∞} {lamN : ℕ → ℝ}
    (sys : ∀ j, System P (j + 1) b (lamN j)) (ω : Ω) : ℕ → ℕ → ℕ → ℝ :=
  fun j k r => (sys j).ξ k r ω

lemma measurable_joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {b : ℕ∞}
    {lamN : ℕ → ℝ} (sys : ∀ j, System P (j + 1) b (lamN j)) : Measurable (joint sys) := by
  refine measurable_pi_lambda _ (fun j => measurable_pi_lambda _
    (fun k => measurable_pi_lambda _ (fun r => (sys j).measurable_ξ k r)))

lemma measurable_coord (j k r : ℕ) : Measurable (fun w : ℕ → ℕ → ℕ → ℝ => w j k r) :=
  (measurable_pi_apply r).comp ((measurable_pi_apply k).comp (measurable_pi_apply j))

/-- The `j`-th system rebuilt on the canonical space `ℕ → ℕ → ℕ → ℝ` (a space in `Type`). -/
noncomputable def liftSys {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (b : ℕ∞) (lamN : ℕ → ℝ) (sys : ∀ j, System P (j + 1) b (lamN j))
    (Q0 : ℕ → ℕ →₀ ℕ) (hocc : ∀ j, IsOccupancy (j + 1) b (Q0 j)) (j : ℕ) :
    System (P.map (joint sys)) (j + 1) b (lamN j) :=
  haveI : IsProbabilityMeasure (P.map (joint sys)) :=
    Measure.isProbabilityMeasure_map (measurable_joint sys).aemeasurable
  { ξ := fun k r w => w j k r
    Q0 := fun _ => Q0 j
    measurable_ξ := fun k r => measurable_coord j k r
    iIndep_ξ := by
      refine (iIndepFun_iff_map_fun_eq_infinitePi_map
        (X := fun (p : ℕ × ℕ) (w : ℕ → ℕ → ℕ → ℝ) => w j p.1 p.2)
        (fun p => measurable_coord j p.1 p.2)).mpr ?_
      have h0 := (sys j).iIndep_ξ.map_fun_eq_infinitePi_map
        (fun (p : ℕ × ℕ) => (sys j).measurable_ξ p.1 p.2)
      have hG : Measurable (fun (w : ℕ → ℕ → ℕ → ℝ) (p : ℕ × ℕ) => w j p.1 p.2) :=
        measurable_pi_lambda _ (fun p => measurable_coord j p.1 p.2)
      rw [Measure.map_map hG (measurable_joint sys)]
      have hm : ∀ p : ℕ × ℕ, (P.map (joint sys)).map (fun w => w j p.1 p.2) =
          P.map ((sys j).ξ p.1 p.2) := fun p => by
        rw [Measure.map_map (measurable_coord j p.1 p.2) (measurable_joint sys)]
        rfl
      simp_rw [hm]
      exact h0
    law_clock := fun k => by
      rw [Measure.map_map (measurable_coord j k 0) (measurable_joint sys)]
      exact (sys j).law_clock k
    law_mark := fun k r hr => by
      rw [Measure.map_map (measurable_coord j k r) (measurable_joint sys)]
      exact (sys j).law_mark k r hr
    measurable_Q0 := fun _ => measurable_const
    isOccupancy_Q0 := fun _ => hocc j
    indep_Q0 := indepFun_const_left _ _ }

lemma liftSys_fluid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (b : ℕ∞) (lamN : ℕ → ℝ) (sys : ∀ j, System P (j + 1) b (lamN j))
    (Q0 : ℕ → ℕ →₀ ℕ) (hocc : ∀ j, IsOccupancy (j + 1) b (Q0 j))
    (hsys : ∀ j ω, (sys j).Q0 ω = Q0 j) (pol : ℕ → Scheme) (j : ℕ) (ω : Ω) (t : ℝ) :
    (liftSys P b lamN sys Q0 hocc j).fluid (pol j) (joint sys ω) t = (sys j).fluid (pol j) ω t := by
  unfold System.fluid System.occ System.stateSeq System.count System.marks
  rw [hsys]
  rfl

end PowerOfDUniversality.Fluid.Thm21Aux

open PowerOfDUniversality.Fluid PowerOfDUniversality.Fluid.Thm21Aux

theorem solution (b : ℕ∞) (hb : 1 ≤ b) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (lamN : ℕ → ℝ) (hlamN : ∀ j, 0 ≤ lamN j)
    (hlim : Tendsto (fun j => lamN j / ((j : ℝ) + 1)) atTop (𝓝 lam))
    (d : ℕ → ℕ) (hd : ∀ j, 1 ≤ d j ∧ d j ≤ j + 1) (hdinf : Tendsto d atTop atTop)
    (qinf : ℕ → ℝ) (hqinf : qinf ∈ FluidSpace b) (Q0 : ℕ → ℕ →₀ ℕ)
    (hQ0 : Tendsto (fun j => l1dist (scaledOcc (j + 1) (Q0 j)) qinf) atTop (𝓝 0))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (sys : ∀ j, System P (j + 1) b (lamN j)) (hsys : ∀ j ω, (sys j).Q0 ω = Q0 j) :
    SubseqFluidLimit P b lam qinf (fun j ω t => (sys j).fluid (jsqd (j + 1) (d j)) ω t) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure P
  have hocc : ∀ j, IsOccupancy (j + 1) b (Q0 j) := fun j => hsys j ω0 ▸ (sys j).isOccupancy_Q0 ω0
  haveI : IsProbabilityMeasure (P.map (joint sys)) :=
    Measure.isProbabilityMeasure_map (measurable_joint sys).aemeasurable
  have key := proposition_4_9 b hb lam hlam0 hlam1 (jsqFluidLimit_of b hb lam hlam0)
  have h := key lamN d Q0 qinf (ℕ → ℕ → ℕ → ℝ) (P.map (joint sys))
    (liftSys P b lamN sys Q0 hocc) hlamN hlim hd hdinf hqinf (fun j ω => rfl) hQ0
  have htr := subseq_transfer P (joint sys) (measurable_joint sys) b lam qinf _ h
  convert htr using 1
  funext j ω t
  exact (liftSys_fluid P b lamN sys Q0 hocc hsys (fun j => jsqd (j + 1) (d j)) j ω t).symm
