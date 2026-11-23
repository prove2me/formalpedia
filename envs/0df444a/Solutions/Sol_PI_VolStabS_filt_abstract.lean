-- Prove2me | solution 1 for PI.VolStabS.filt_abstract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:36.479326+00:00
-- url     : https://prove2.me/submissions/8fb87584-2379-4b1e-8b1c-ff4791c091a9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_EventuallySmulSub
import Theorems.Thm_PI_VolStabS_mem_smulSub
import Theorems.Thm_PI_VolStabS_coe_smulSub
import Theorems.Thm_PI_VolStabS_isOpen_smulSub
import Theorems.Thm_PI_VolStabS_isCompact_smulSub
import Theorems.Thm_PI_VolStabS_eventually_smul_sub
import Theorems.Thm_PI_VolStabS_reach_of_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
variable [T2Space X]
namespace PI.VolStabS
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
  have hβ0 : ∀ w, β 0 w = 0 := fun w => by
    have h := hβ1 0 0 w
    rw [add_zero] at h
    simpa using h
  have hβ0' : ∀ u, β u 0 = 0 := fun u => by
    have h := hβ2 u 0 0
    rw [add_zero] at h
    simpa using h
  let Dm : V → V →+ X := fun u =>
    { toFun := β u, map_zero' := hβ0' u, map_add' := hβ2 u }
  have hDm : ∀ u w, Dm u w = β u w := fun _ _ => rfl
  have hDmc : ∀ u, Continuous (Dm u) := fun u =>
    hβc.comp (Continuous.prodMk continuous_const continuous_id)
  set P : AddSubgroup X := L.map (Dm x) with hPdef
  have hPset : (P : Set X) = β x '' (L : Set V) := by
    rw [hPdef, AddSubgroup.coe_map]
    rfl
  have hPo : IsOpen (P : Set X) := by rw [hPset]; exact hxo
  have hPc : IsCompact (P : Set X) := by rw [hPset]; exact hLc.image (hDmc x)
  have hπP : ∀ p ∈ P, π • p ∈ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    exact AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, by rw [hDm, hDm, hβs]⟩
  have hπkP : ∀ k : ℕ, ∀ p ∈ P, π ^ k • p ∈ P := by
    intro k
    induction k with
    | zero => intro p hp; simpa using hp
    | succ k ih =>
      intro p hp
      rw [pow_succ, mul_smul]
      exact ih _ (hπP p hp)
  set πP := smulSub π P with hπPdef
  have hπPo : IsOpen (πP : Set X) := isOpen_smulSub π hπ0 P hPo
  have hN1 : ∀ᶠ u in 𝓝 (0 : V), ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X) := by
    have hP : ∀ w ∈ (L : Set V), ∀ᶠ q : V × V in 𝓝 ((0 : V), w), β q.1 q.2 ∈ (πP : Set X) := by
      intro w _
      have h := hβc.tendsto ((0 : V), w)
      have hm : β ((0 : V), w).1 ((0 : V), w).2 ∈ (πP : Set X) := by
        show β 0 w ∈ (πP : Set X)
        rw [hβ0]
        exact πP.zero_mem
      exact h (hπPo.mem_nhds hm)
    exact hLc.eventually_forall_of_forall_eventually
      (P := fun (u : V) (w : V) => β u w ∈ (πP : Set X)) hP
  obtain ⟨N2, hN2, hsm⟩ := hsmall πP (hπPo.mem_nhds πP.zero_mem)
  refine ⟨{u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2, inter_mem hN1 hN2, ?_⟩
  rintro y hy Λ0 ⟨c, hc0, rfl⟩ hsub
  have hcL : ∀ w ∈ L, c • w ∈ {u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2 :=
    fun w hw => hsub (AddSubgroup.mem_map.2 ⟨w, hw, rfl⟩)
  have hcG : ∀ w ∈ L, c • G w ∈ πP := hsm c (fun w hw => (hcL w hw).2)
  have hreach : ∀ p ∈ P, ∃ l ∈ L, Dm y l = p := by
    refine reach_of_approx π hπ L hLc hπL (Dm y) (hDmc y) (fun t w => hβs t y w) P hPc ?_
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    refine ⟨l, hl, ?_⟩
    have e : Dm x l - Dm y l = -(β (y - x) l) := by
      rw [hDm, hDm]
      have := hβ1 x (y - x) l
      rw [add_sub_cancel] at this
      rw [this]
      abel
    rw [e]
    exact πP.neg_mem (hy.1 l hl)
  set Q := L.map (Dm y) with hQdef
  have hPQ : P ≤ Q := fun p hp => by
    obtain ⟨l, hl, e⟩ := hreach p hp
    exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  have hQo : IsOpen (Q : Set X) := AddSubgroup.isOpen_mono hPQ hPo
  have hQc : IsCompact (Q : Set X) := by rw [hQdef, AddSubgroup.coe_map]; exact hLc.image (hDmc y)
  set s : ℕ → K := fun n => π ^ n * c with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero n hπ0) hc0
  have hsc : s 0 = c := by simp [hsdef]
  set Λ : ℕ → AddSubgroup V := fun n => smulSub (s n) L with hΛdef
  have hH : ∀ n, (Λ n).map (Dm y) = smulSub (s n) Q := by
    intro n
    ext z
    rw [AddSubgroup.mem_map, mem_smulSub]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hv
      exact ⟨Dm y l, AddSubgroup.mem_map_of_mem _ hl, by rw [hDm, hDm, hβs]⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
      exact ⟨s n • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, by rw [hDm, hDm, hβs]⟩
  refine ⟨Λ, fun n => (Λ n).map (Dm y), Dm y, ?_, fun n => isOpen_smulSub _ (hs0 n) L hLo,
    fun n => isCompact_smulSub _ L hLc, ?_, ?_, ?_, ?_, fun n => rfl, ?_⟩
  · simp only [hΛdef, smulSub, hsc]
  · refine antitone_nat_of_succ_le fun n z hz => ?_
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hz
    refine (mem_smulSub _ _ _).2 ⟨π • l, hπL l hl, ?_⟩
    rw [smul_smul]
    congr 1
    simp only [hsdef]
    ring
  · intro n
    show IsOpen (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isOpen_smulSub _ (hs0 n) Q hQo
  · intro n
    show IsCompact (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isCompact_smulSub _ Q hQc
  · intro N' hN'
    have hst : Tendsto s atTop (𝓝 0) := by
      have := hπ.mul_const c
      simpa [hsdef] using this
    obtain ⟨k, hk⟩ := eventually_smul_sub (Q : Set X) hQc s hst N' hN'
    refine ⟨k, ?_⟩
    show (((Λ k).map (Dm y) : AddSubgroup X) : Set X) ⊆ N'
    rw [hH, coe_smulSub]
    rintro _ ⟨q, hq, rfl⟩
    exact hk q hq
  · intro n Z hZ W hW
    obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hsc]
    show G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) ∈ (Λ (n + 1)).map (Dm y)
    have e1 : G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) =
        β (c • z) (s n • w) + G (s n • w) := by
      rw [hG (y + c • z) (s n • w), hβ1 y (c • z)]
      abel
    obtain ⟨p1, hp1, e2⟩ := (mem_smulSub _ _ _).1 ((hcL z hz).1 w hw)
    obtain ⟨p2, hp2, e3⟩ := (mem_smulSub _ _ _).1 (hcG w hw)
    have e4 : β (c • z) (s n • w) + G (s n • w) = s (n + 1) • (p1 + π ^ n • p2) := by
      rw [hβs, hGs, ← e2]
      have e5 : s n • s n • G w = s n • π ^ n • (c • G w) := by
        simp only [hsdef]
        module
      rw [e5, ← e3]
      simp only [hsdef]
      module
    rw [e1, e4, hH]
    exact (mem_smulSub _ _ _).2 ⟨_, hPQ (P.add_mem hp1 (hπkP n p2 hp2)), rfl⟩
end PI.VolStabS
