-- Prove2me | solution 1 for PI.LevelKSplit.W.NCA.conjNH_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:50.2521+00:00
-- url     : https://prove2.me/submissions/69e2bc1f-3e5a-4602-af80-478885621e7a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCAsmM
import Theorems.Thm_PI_LevelKSplit_W_NCA_conjInv_of_one
import Theorems.Thm_PI_LevelKSplit_W_ExC_closed_SNH
import Theorems.Thm_PI_LevelKSplit_W_ExS_lcsc_HAf
import Theorems.Thm_PI_LevelKSplit_W_NCA_mem_Wp_iff
import Theorems.Thm_PI_LevelKSplit_W_NCA_sc_tens
import Theorems.Thm_PI_LevelKSplit_W_NCA_wp_map
import Theorems.Thm_PI_LevelKSplit_W_SC_finite_adeles_secondCountable
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp
import Theorems.Thm_PI_VolSemiDirect_W_subgroup_locally_compact_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
namespace PI.LevelKSplit.W.NCA
theorem _root_.solution (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)
end PI.LevelKSplit.W.NCA
