-- Prove2me | solution 1 for PI.VolStabSW.OmFibG.gramFilt_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:30.661804+00:00
-- url     : https://prove2.me/submissions/39f0d458-1547-49a0-9f5c-503bcfd688bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVDx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVSec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_FibExGram
import Theorems.Thm_PI_VolStabSW_OmFibG_dxOpen_gen
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_continuous_crd
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_crd_incl
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isClopen_latV
import Theorems.Thm_PI_VolStabSW_PositiveNearLattice_isCompact_latV
import Theorems.Thm_PI_VolStabSW_continuous_gramB
import Theorems.Thm_PI_VolStabSW_continuous_gramH
import Theorems.Thm_PI_VolStabSW_exists_unif_Fv
import Theorems.Thm_PI_VolStabSW_filt_abstract
import Theorems.Thm_PI_VolStabSW_gramB_mem
import Theorems.Thm_PI_VolStabSW_hR_add_left
import Theorems.Thm_PI_VolStabSW_hR_add_right
import Theorems.Thm_PI_VolStabSW_hR_smul_left
import Theorems.Thm_PI_VolStabSW_hR_smul_right
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OmFibG
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct
namespace PI.VolStabSW.OmFibG
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (a : ℕ) (ha1 : 1 ≤ a)
    (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (x : Fin a → Fin M → Fv F v ⊗[F] E) (hx : LinearIndependent (Fv F v ⊗[F] E) x) :
    FiltConcl σ hσ M J hJ a v d b x := by
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : ContinuousSMul (Fv F v) (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (Fv F v) (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
      p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  obtain ⟨π, hπ0, hπ, hπO⟩ := exists_unif_Fv v
  set L := latSub b v a M with hLdef
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := by
    intro w hw i j k
    have h := hw i j k
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (π • w i j) k ∈ v.adicCompletionIntegers F
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hπO h
  let β : (Fin a → Fin M → Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) →
      HermR (Fv F v) σ a := fun u w => ⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ u w⟩
  have hβc : Continuous fun q : (Fin a → Fin M → Fv F v ⊗[F] E) × (Fin a → Fin M → Fv F v ⊗[F] E) =>
      β q.1 q.2 := (continuous_gramB (Fv F v) σ J).subtype_mk _
  have hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w := by
    intro u u' w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J (u + u') w i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u' w i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβ2 : ∀ u w w', β u (w + w') = β u w + β u w' := by
    intro u w w'
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (w + w') i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u w' i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβs : ∀ (t : Fv F v) u w, β u (t • w) = t • β u w := by
    intro t u w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (t • w) i j = t • gramB (Fv F v) σ J u w i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]
  set G := gramH (Fv F v) σ hσ J hJ (n := a) with hGdef
  have hG : ∀ u W, G (u + W) = G u + β u W + G W := by
    intro u W
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (u + W) i j =
      gramR (Fv F v) σ J u i j + gramB (Fv F v) σ J u W i j + gramR (Fv F v) σ J W i j
    simp only [gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hGs : ∀ (t : Fv F v) w, G (t • w) = t • t • G w := by
    intro t w
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j
    simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]
  have hGc : Continuous G := continuous_gramH (Fv F v) σ hσ J hJ
  have hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by
    have h := dxOpen_gen σ hσ M J hJ hdet a v d b x hx
    have e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) = β x := by
      funext W
      rw [← hGdef, hG]
      abel
    rwa [e] at h

  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exfalso
      have : (1 : E) = 0 := by
        rw [← b.sum_repr (1 : E)]
        simp
      exact one_ne_zero this
    · exact h0
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0
      exfalso
      have : Nontrivial (Fv F v ⊗[F] E) := inferInstance
      exact hx.ne_zero ⟨0, ha1⟩ (funext fun j => j.elim0)
    · exact h0
  let i0 : Fin a := ⟨0, ha1⟩
  let j0 : Fin M := ⟨0, hM⟩
  let k0 : Fin d := ⟨0, hd⟩
  let φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v := fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0
  have hφc : Continuous φ :=
    (PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))
  have hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y := by
    intro t Y
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 =
      t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e0 : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0
  have he0L : e0 ∈ L := by
    intro i j k
    show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F
    by_cases hij : i = i0 ∧ j = j0
    · simp only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply]
      split_ifs
      · simp
      · simp
    · simp only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]
      exact zero_mem _
  have hφe : φ e0 = 1 := by
    show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1
    simp [e0, PositiveNearLattice.crd_incl, b.repr_self]
  have hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E),
      ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U := by
    intro U hU
    have hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
        t • G w ∈ U := by
      have hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
          ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U := by
        intro w _
        have h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)
            (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a)) := by
          have hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) :=
            continuous_fst.smul (hGc.comp continuous_snd)
          have := hc.tendsto ((0 : Fv F v), w)
          simpa using this
        exact h hU
      exact hLc.eventually_forall_of_forall_eventually
        (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP
    refine ⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩
    · have h0 : φ 0 = 0 := by
        have := hφs 0 0
        simpa using this
      exact hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)
    · intro c hc w hw
      have h := hc e0 he0L
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h
      exact h w hw
  exact filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall
end PI.VolStabSW.OmFibG
