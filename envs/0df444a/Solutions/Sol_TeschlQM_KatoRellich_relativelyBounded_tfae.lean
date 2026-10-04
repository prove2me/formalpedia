-- Prove2me | solution 1 for TeschlQM.KatoRellich.relativelyBounded_tfae
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:07:26.9808+00:00
-- url     : https://prove2.me/submissions/049f3a28-8135-4b9a-bfa5-b96085eee57c

import Mathlib
import Definitions.Def_TeschlQM_KatoRellich_IsRelativelyBounded
import Definitions.Def_TeschlQM_KatoRellich_resolvent
import Definitions.Def_TeschlQM_KatoRellich_compCLM
import Definitions.Def_TeschlQM_KatoRellich_opNorm

open Filter Topology
open scoped ENNReal

namespace TeschlQM.KatoRellich

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolvent_spec_core (A : H →ₗ.[ℂ] H) {z : ℂ} (hz : z ∈ resolventSet A) :
    IsResolventAt A z (resolvent A z) := by
  have h : ∃ R : H →L[ℂ] H, IsResolventAt A z R := hz
  simp only [resolvent, dif_pos h]
  exact h.choose_spec

lemma mem_compCLM_domain_core (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (φ : H) :
    φ ∈ (compCLM B R).domain ↔ R φ ∈ B.domain := Iff.rfl

lemma compCLM_apply_core (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (φ : (compCLM B R).domain) :
    compCLM B R φ = B ⟨R φ, φ.2⟩ := rfl

lemma domain_eq_top_core (A B : H →ₗ.[ℂ] H) {z : ℂ} {R : H →L[ℂ] H} (hR : IsResolventAt A z R)
    (h2 : A.domain ≤ B.domain) : (compCLM B R).domain = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  rw [mem_compCLM_domain_core]
  obtain ⟨hm, -⟩ := hR.1 φ
  exact h2 hm

lemma mem_of_domain_top_core (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H)
    (hdom : (compCLM B R).domain = ⊤) (φ : H) : R φ ∈ B.domain := by
  have : φ ∈ (compCLM B R).domain := by rw [hdom]; trivial
  exact this

/-- The everywhere defined map `φ ↦ B (R φ)`. -/
noncomputable def totalMap_core (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H)
    (hdom : (compCLM B R).domain = ⊤) : H →ₗ[ℂ] H :=
  (compCLM B R).toFun.comp (LinearMap.codRestrict (compCLM B R).domain LinearMap.id
    (fun φ => by rw [hdom]; trivial))

lemma totalMap_core_apply (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hdom : (compCLM B R).domain = ⊤)
    (φ : H) (h : R φ ∈ B.domain) : totalMap_core B R hdom φ = B ⟨R φ, h⟩ := rfl

/-- Closed graph theorem: `B R` is bounded when `A` is closed, `B` closable and `𝔇(A) ⊆ 𝔇(B)`. -/
lemma continuous_totalMap_core (A B : H →ₗ.[ℂ] H) (hB : B.IsClosable) {z : ℂ} {R : H →L[ℂ] H}
    (_hR : IsResolventAt A z R) (hdom : (compCLM B R).domain = ⊤) :
    Continuous (totalMap_core B R hdom) := by
  apply LinearMap.continuous_of_isClosed_graph
  refine IsSeqClosed.isClosed ?_
  intro p q hp hlim
  rw [SetLike.mem_coe, LinearMap.mem_graph_iff]
  have hp' : ∀ n, (p n).2 = totalMap_core B R hdom (p n).1 := fun n =>
    (LinearMap.mem_graph_iff _ _).mp (hp n)
  have hmem := mem_of_domain_top_core B R hdom
  have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hlim
  have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 q.2) := (continuous_snd.tendsto q).comp hlim
  have hR1 : Tendsto (fun n => R (p n).1) atTop (𝓝 (R q.1)) := (R.continuous.tendsto _).comp h1
  have hseq : Tendsto (fun n => (R (p n).1, (p n).2)) atTop (𝓝 (R q.1, q.2)) := hR1.prodMk_nhds h2
  have hle := LinearPMap.le_closure B
  have hin : ∀ n, (R (p n).1, (p n).2) ∈ (B.closure.graph : Set (H × H)) := by
    intro n
    rw [hp' n, totalMap_core_apply B R hdom _ (hmem _), SetLike.mem_coe, LinearPMap.mem_graph_iff]
    refine ⟨⟨R (p n).1, hle.1 (hmem _)⟩, rfl, ?_⟩
    exact (hle.2 (x := ⟨R (p n).1, hmem _⟩) (y := ⟨R (p n).1, hle.1 (hmem _)⟩) rfl).symm
  have hcl : (R q.1, q.2) ∈ (B.closure.graph : Set (H × H)) :=
    hB.closure_isClosed.mem_of_tendsto hseq (Eventually.of_forall hin)
  rw [SetLike.mem_coe, LinearPMap.mem_graph_iff] at hcl
  obtain ⟨y, hy1, hy2⟩ := hcl
  rw [totalMap_core_apply B R hdom _ (hmem _), ← hy2]
  exact (hle.2 (x := ⟨R q.1, hmem _⟩) (y := y) hy1.symm).symm

lemma opNorm_lt_top_core (B : H →ₗ.[ℂ] H) (R : H →L[ℂ] H) (hdom : (compCLM B R).domain = ⊤)
    (hcont : Continuous (totalMap_core B R hdom)) : opNorm (compCLM B R) < ⊤ := by
  let Tc : H →L[ℂ] H := ⟨totalMap_core B R hdom, hcont⟩
  have hle : opNorm (compCLM B R) ≤ (‖Tc‖₊ : ℝ≥0∞) := by
    refine iSup_le fun φ => ?_
    refine ENNReal.div_le_of_le_mul ?_
    have e : compCLM B R φ = Tc (φ : H) := rfl
    have : ‖compCLM B R φ‖₊ ≤ ‖Tc‖₊ * ‖(φ : H)‖₊ := by rw [e]; exact Tc.le_opNNNorm _
    exact_mod_cast this
  exact lt_of_le_of_lt hle ENNReal.coe_lt_top

/-- A finite `‖B R_A(z)‖` gives constants for relative boundedness. -/
lemma relBounded_of_opNorm_core (A B : H →ₗ.[ℂ] H) {z : ℂ} {R : H →L[ℂ] H}
    (hR : IsResolventAt A z R) (hdom : (compCLM B R).domain = ⊤)
    (hfin : opNorm (compCLM B R) ≠ ⊤) :
    IsRelativelyBoundedWith A B (opNorm (compCLM B R)).toReal
      ((opNorm (compCLM B R)).toReal * ‖z‖) := by
  set C := (opNorm (compCLM B R)).toReal with hC
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  have hmem := mem_of_domain_top_core B R hdom
  have hbound : ∀ (φ : H) (h : R φ ∈ B.domain), ‖B ⟨R φ, h⟩‖ ≤ C * ‖φ‖ := by
    intro φ h
    by_cases hφ : φ = 0
    · subst hφ
      have : (⟨R 0, h⟩ : B.domain) = 0 := Subtype.ext (by simp)
      rw [this, LinearPMap.map_zero, norm_zero]; simp
    · have hφdom : φ ∈ (compCLM B R).domain := by rw [hdom]; trivial
      have hsup : (‖compCLM B R ⟨φ, hφdom⟩‖₊ : ℝ≥0∞) / ‖φ‖₊ ≤ opNorm (compCLM B R) :=
        le_iSup (fun ψ : (compCLM B R).domain => (‖compCLM B R ψ‖₊ : ℝ≥0∞) / ‖(ψ : H)‖₊) ⟨φ, hφdom⟩
      rw [compCLM_apply_core] at hsup
      have hφ' : (‖φ‖₊ : ℝ≥0∞) ≠ 0 := by simpa using hφ
      rw [ENNReal.div_le_iff hφ' ENNReal.coe_ne_top] at hsup
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top hfin ENNReal.coe_ne_top) hsup
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, coe_nnnorm, coe_nnnorm] at this
      exact this
  refine ⟨?_, hC0, by positivity, ?_⟩
  · intro ψ hψ
    have e : R (A ⟨ψ, hψ⟩ - z • ψ) = ψ := hR.2 ⟨ψ, hψ⟩
    rw [← e]; exact hmem _
  · intro ψ hA hB'
    have e : R (A ⟨ψ, hA⟩ - z • ψ) = ψ := hR.2 ⟨ψ, hA⟩
    have hsub : (⟨ψ, hB'⟩ : B.domain) = ⟨R (A ⟨ψ, hA⟩ - z • ψ), hmem _⟩ := Subtype.ext e.symm
    rw [hsub]
    calc ‖B ⟨R (A ⟨ψ, hA⟩ - z • ψ), hmem _⟩‖ ≤ C * ‖A ⟨ψ, hA⟩ - z • ψ‖ := hbound _ _
      _ ≤ C * (‖A ⟨ψ, hA⟩‖ + ‖z‖ * ‖ψ‖) := by
        gcongr
        calc ‖A ⟨ψ, hA⟩ - z • ψ‖ ≤ ‖A ⟨ψ, hA⟩‖ + ‖z • ψ‖ := norm_sub_le _ _
          _ = ‖A ⟨ψ, hA⟩‖ + ‖z‖ * ‖ψ‖ := by rw [norm_smul]
      _ = C * ‖A ⟨ψ, hA⟩‖ + C * ‖z‖ * ‖ψ‖ := by ring

end TeschlQM.KatoRellich

open TeschlQM.KatoRellich in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A B : H →ₗ.[ℂ] H) (hA : A.IsClosed) (hB : B.IsClosable)
    (hρ : (resolventSet A).Nonempty) :
    [IsRelativelyBounded A B,
      A.domain ≤ B.domain,
      ∃ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤,
      ∀ z ∈ resolventSet A, (compCLM B (resolvent A z)).domain = ⊤ ∧
        opNorm (compCLM B (resolvent A z)) < ⊤].TFAE ∧
    (IsRelativelyBounded A B →
      relativeBound A B ≤ ⨅ z ∈ resolventSet A, opNorm (compCLM B (resolvent A z))) := by
  constructor
  · tfae_have 1 → 2 := fun ⟨a, b, h⟩ => h.1
    tfae_have 2 → 4 := by
      intro h2 z hz
      have hR := resolvent_spec_core A hz
      have hdom := domain_eq_top_core A B hR h2
      exact ⟨hdom, opNorm_lt_top_core B _ hdom (continuous_totalMap_core A B hB hR hdom)⟩
    tfae_have 4 → 3 := by
      intro h4
      obtain ⟨z, hz⟩ := hρ
      exact ⟨z, hz, h4 z hz⟩
    tfae_have 3 → 1 := by
      rintro ⟨z, hz, hdom, hlt⟩
      exact ⟨_, _, relBounded_of_opNorm_core A B (resolvent_spec_core A hz) hdom hlt.ne⟩
    tfae_finish
  · intro h1
    refine le_iInf₂ fun z hz => ?_
    by_cases hfin : opNorm (compCLM B (resolvent A z)) = ⊤
    · rw [hfin]; exact le_top
    · obtain ⟨a, b, hab⟩ := h1
      have hR := resolvent_spec_core A hz
      have hdom := domain_eq_top_core A B hR hab.1
      have hw := relBounded_of_opNorm_core A B hR hdom hfin
      calc relativeBound A B ≤ ENNReal.ofReal (opNorm (compCLM B (resolvent A z))).toReal :=
            iInf₂_le _ ⟨_, hw⟩
        _ = _ := ENNReal.ofReal_toReal hfin

#print axioms solution
