-- Prove2me | solution 1 for PI.VolStabSW.reach_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:40.548206+00:00
-- url     : https://prove2.me/submissions/44e83cdb-d6f4-41da-a399-b25fc6ceda08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub
import Theorems.Thm_PI_VolStabSW_mem_smulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
variable [T2Space X]
namespace PI.VolStabSW
theorem _root_.solution (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  classical
  have hbase' : ∀ p ∈ P, ∃ l ∈ L, ∃ q ∈ P, π • q = p - D l := fun p hp => by
    obtain ⟨l, hl, h⟩ := hbase p hp
    exact ⟨l, hl, (mem_smulSub π P _).1 h⟩
  choose! fl hfl fq hfq hrel using hbase'
  intro p hp

  let ps : ℕ → X := fun k => Nat.rec p (fun _ q => fq q) k
  have hpsS : ∀ k, ps (k + 1) = fq (ps k) := fun k => rfl
  have hpsP : ∀ k, ps k ∈ P := by
    intro k
    induction k with
    | zero => exact hp
    | succ k ih => rw [hpsS]; exact hfq _ ih
  have hπLk : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => intro w hw; rw [pow_succ, mul_smul]; exact ih _ (hπL w hw)
  let σ : ℕ → V := fun k => ∑ i ∈ Finset.range (k + 1), π ^ i • fl (ps i)
  have hσL : ∀ k, σ k ∈ L := fun k => L.sum_mem fun i _ => hπLk i _ (hfl _ (hpsP i))
  have hrem : ∀ k, p - D (σ k) = π ^ (k + 1) • ps (k + 1) := by
    intro k
    induction k with
    | zero =>
      show p - D (∑ i ∈ Finset.range 1, π ^ i • fl (ps i)) = π ^ 1 • fq p
      rw [Finset.sum_range_one, pow_zero, one_smul, pow_one, hrel p hp]
      rfl
    | succ k ih =>
      have e1 : σ (k + 1) = σ k + π ^ (k + 1) • fl (ps (k + 1)) := Finset.sum_range_succ _ _
      rw [hpsS (k + 1), e1, map_add, hDs, sub_add_eq_sub_sub, ih, ← smul_sub,
        ← hrel _ (hpsP (k + 1)), smul_smul, ← pow_succ]

  have hsmallP : ∀ N ∈ 𝓝 (0 : X), ∀ᶠ c in 𝓝 (0 : K), ∀ q ∈ P, c • q ∈ N := fun N hN =>
    hPc.eventually_forall_of_forall_eventually fun q _ => by
      have h0 : Tendsto (fun z : K × X => z.1 • z.2) (𝓝 ((0 : K), q)) (𝓝 ((0 : K) • q)) :=
        continuous_smul.continuousAt
      rw [zero_smul] at h0
      exact h0 hN
  have hπ1 : Tendsto (fun k : ℕ => π ^ (k + 1)) atTop (𝓝 0) := hπ.comp (tendsto_add_atTop_nat 1)
  have hremT : Tendsto (fun k => p - D (σ k)) atTop (𝓝 0) := by
    refine Tendsto.congr (fun k => (hrem k).symm) ?_
    intro N hN
    exact (hπ1.eventually (hsmallP N hN)).mono fun k hk => hk _ (hpsP (k + 1))
  have hDT : Tendsto (fun k => D (σ k)) atTop (𝓝 p) := by
    simpa using (tendsto_const_nhds (x := p)).sub hremT

  obtain ⟨l, hlL, hcl⟩ := hLc (f := Filter.map σ atTop)
    (Filter.le_principal_iff.2 (Filter.mem_map.2 (Filter.univ_mem' hσL)))
  refine ⟨l, hlL, ?_⟩
  have h2 : MapClusterPt (D l) atTop (D ∘ σ) := MapClusterPt.continuousAt_comp hDc.continuousAt hcl
  exact eq_of_nhds_neBot ((show ClusterPt (D l) (Filter.map (D ∘ σ) atTop) from h2).neBot.mono
    (inf_le_inf_left _ hDT))
end PI.VolStabSW
