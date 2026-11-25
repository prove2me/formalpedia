-- Prove2me | solution 1 for PI.VolStabSW.filt_abstract
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:47.406453+00:00
-- url     : https://prove2.me/submissions/322d3da2-6b6b-4c61-ad70-39af481a3dcf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_EventuallySmulSub
import Theorems.Thm_PI_VolStabSW_mem_smulSub
import Theorems.Thm_PI_VolStabSW_isOpen_smulSub
import Theorems.Thm_PI_VolStabSW_isCompact_smulSub
import Theorems.Thm_PI_VolStabSW_eventually_smul_sub
import Theorems.Thm_PI_VolStabSW_reach_of_approx

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
theorem _root_.solution [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribMulAction.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) := by
  classical
  have hβ0 : ∀ w, β 0 w = 0 := fun w => by simpa using hβ1 0 0 w
  have hβcont : ∀ u, Continuous fun w => β u w := fun u =>
    hβc.comp (continuous_const.prodMk continuous_id)
  have hπLk : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => intro w hw; rw [pow_succ, mul_smul]; exact ih _ (hπL w hw)

  let Dx : V →+ X := AddMonoidHom.mk' (β x) (hβ2 x)
  let A : AddSubgroup X := L.map Dx
  have hAcoe : (A : Set X) = β x '' (L : Set V) := AddSubgroup.coe_map _ _
  have hAo : IsOpen (A : Set X) := by rw [hAcoe]; exact hxo
  have hAc : IsCompact (A : Set X) := by rw [hAcoe]; exact hLc.image (hβcont x)
  let U : AddSubgroup X := smulSub π A
  have hUo : IsOpen (U : Set X) := isOpen_smulSub π hπ0 A hAo
  have hU : (U : Set X) ∈ 𝓝 (0 : X) := hUo.mem_nhds U.zero_mem
  have hUA : ∀ a ∈ U, a ∈ A := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := (mem_smulSub π A a).1 ha
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 ha'
    exact AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, hβs π x l⟩

  have hN3 : ∀ᶠ Z in 𝓝 (0 : V), ∀ w ∈ L, β Z w ∈ U :=
    hLc.eventually_forall_of_forall_eventually fun w _ => by
      have h0 : Tendsto (fun q : V × V => β q.1 q.2) (𝓝 ((0 : V), w)) (𝓝 (β 0 w)) :=
        hβc.continuousAt
      rw [hβ0] at h0
      exact h0 hU
  obtain ⟨N2, hN2, hN2'⟩ := hsmall U hU
  refine ⟨N2 ∩ {Z | ∀ w ∈ L, β Z w ∈ U}, inter_mem hN2 hN3, ?_⟩
  rintro y ⟨-, hyN3⟩ Λ0 ⟨c, hc0, rfl⟩ hΛ0N

  let Dy : V →+ X := AddMonoidHom.mk' (β y) (hβ2 y)
  have hDy : ∀ w, Dy w = β y w := fun w => rfl
  have hDys : ∀ (t : K) w, Dy (t • w) = t • Dy w := fun t w => hβs t y w
  have hβy : ∀ w, β y w = β x w + β (y - x) w := fun w => by
    rw [← hβ1, add_sub_cancel]
  have hAy : L.map Dy = A := by
    ext a
    constructor
    · intro ha
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 ha
      rw [hDy, hβy]
      exact A.add_mem (AddSubgroup.mem_map.2 ⟨l, hl, rfl⟩) (hUA _ (hyN3 l hl))
    · intro ha
      refine AddSubgroup.mem_map.2 ?_
      refine reach_of_approx π hπ L hLc hπL Dy (hβcont y) hDys A hAc ?_ a ha
      intro p hp
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
      refine ⟨l, hl, ?_⟩
      have e : Dx l - Dy l = -β (y - x) l := by
        show β x l - β y l = _
        rw [hβy]; abel
      rw [e]
      exact U.neg_mem (hyN3 l hl)

  have hmapS : ∀ (t : K) (P : AddSubgroup V), (smulSub t P).map Dy = smulSub t (P.map Dy) := by
    intro t P
    ext z
    simp only [AddSubgroup.mem_map, mem_smulSub]
    constructor
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Dy p, ⟨p, hp, rfl⟩, (hDys t p).symm⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨t • p, ⟨p, hp, rfl⟩, hDys t p⟩
  let Λ : ℕ → AddSubgroup V := fun n => smulSub (π ^ n) (smulSub c L)
  let H : ℕ → AddSubgroup X := fun n => (Λ n).map Dy
  have hH : ∀ n, H n = smulSub (π ^ n) (smulSub c A) := fun n => by
    show (smulSub (π ^ n) (smulSub c L)).map Dy = _
    rw [hmapS, hmapS, hAy]
  have hΛ0 : Λ 0 = smulSub c L := by
    ext z
    simp only [Λ, mem_smulSub, pow_zero, one_smul]
    exact ⟨fun ⟨p, hp, e⟩ => e ▸ hp, fun h => ⟨z, h, rfl⟩⟩
  have hcL : IsOpen (smulSub c L : Set V) := isOpen_smulSub c hc0 L hLo
  have hcLc : IsCompact (smulSub c L : Set V) := isCompact_smulSub c L hLc
  refine ⟨Λ, H, Dy, hΛ0, fun n => isOpen_smulSub _ (pow_ne_zero n hπ0) _ hcL,
    fun n => isCompact_smulSub _ _ hcLc, ?_, fun n => ?_, fun n => ?_, ?_, fun n => rfl, ?_⟩
  · refine antitone_nat_of_succ_le fun n => ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := (mem_smulSub _ _ z).1 hz
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub c L p).1 hp
    refine (mem_smulSub _ _ _).2 ⟨c • (π • l), (mem_smulSub c L _).2 ⟨π • l, hπL l hl, rfl⟩, ?_⟩
    rw [smul_comm c π l, smul_smul, ← pow_succ]
  · rw [hH]
    exact isOpen_smulSub _ (pow_ne_zero n hπ0) _ (isOpen_smulSub c hc0 A hAo)
  · show IsCompact ((Λ n).map Dy : Set X)
    rw [AddSubgroup.coe_map]
    exact (isCompact_smulSub _ _ hcLc).image (hβcont y)
  · intro N' hN'
    obtain ⟨k, hk⟩ := eventually_smul_sub (smulSub c A : Set X) (isCompact_smulSub c A hAc)
      (fun k => π ^ k) hπ N' hN'
    refine ⟨k, fun z hz => ?_⟩
    rw [hH] at hz
    obtain ⟨p, hp, rfl⟩ := (mem_smulSub _ _ z).1 hz
    exact hk p hp
  · intro n Z hZ W hW
    rw [hΛ0] at hZ
    have hZN := (hΛ0N hZ).2
    obtain ⟨z, hz, rfl⟩ := (mem_smulSub c L Z).1 hZ
    obtain ⟨W', hW', rfl⟩ := (mem_smulSub _ _ W).1 hW
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub c L W').1 hW'
    set t : K := π ^ n * c with ht
    have e1 : G (y + c • z + π ^ n • c • w) - G (y + c • z) - Dy (π ^ n • c • w)
        = t • (β (c • z) w + t • G w) := by
      rw [hG (y + c • z), hβ1, hDy]
      simp only [ht, hβs, hGs]
      module
    rw [e1]

    have hu1 : β (c • z) w ∈ U := hZN w hw
    have hu2 : t • G w ∈ U := by
      refine hN2' t (fun w' hw' => (hΛ0N ?_).1) w hw
      refine (mem_smulSub c L _).2 ⟨π ^ n • w', hπLk n w' hw', ?_⟩
      rw [smul_smul, ht, mul_comm]
    obtain ⟨a, ha, hae⟩ := (mem_smulSub π A _).1 (U.add_mem hu1 hu2)
    rw [← hAy] at ha
    obtain ⟨l', hl', rfl⟩ := AddSubgroup.mem_map.1 ha
    rw [← hae]
    refine AddSubgroup.mem_map.2 ⟨π ^ (n + 1) • c • l', (mem_smulSub _ _ _).2
      ⟨c • l', (mem_smulSub c L _).2 ⟨l', hl', rfl⟩, rfl⟩, ?_⟩
    rw [hDys, hDys, smul_smul, smul_smul, ht]
    congr 1
    ring
end PI.VolStabSW
