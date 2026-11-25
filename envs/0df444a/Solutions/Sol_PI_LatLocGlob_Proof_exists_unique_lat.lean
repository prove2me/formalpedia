-- Prove2me | solution 1 for PI.LatLocGlob.Proof.exists_unique_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:41.004387+00:00
-- url     : https://prove2.me/submissions/14140bb4-0306-4b73-a0f7-0fa39fcfd081

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal
import Theorems.Thm_PI_LatLocGlob_Proof_mem_locSub
import Theorems.Thm_PI_LatLocGlob_Proof_mem_loc_of_mem
import Theorems.Thm_PI_LatLocGlob_Proof_mem_loc_of_smul
import Theorems.Thm_PI_LatLocGlob_Proof_mem_of_forall_loc
import Theorems.Thm_PI_LatLocGlob_Proof_commonMult
import Theorems.Thm_PI_LatLocGlob_Proof_exists_smul_mem
import Theorems.Thm_PI_LatLocGlob_Proof_exists_smul_le
import Theorems.Thm_PI_LatLocGlob_Proof_exists_smul_mem_of_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R K V : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace PI.LatLocGlob.Proof
theorem _root_.solution (L0 : Submodule R V) (hL0 : IsFullLat K L0) (M : Ideal R → Set V)
    (hM : ∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N)
    (hfin : Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0}) :
    ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p := by
  classical
  obtain ⟨hL0fg, hL0sp⟩ := hL0
  choose! N hNfull hMN using hM
  have hMsmul : ∀ q : Ideal R, q.IsMaximal → ∀ (r : R) (y : V), y ∈ M q → r • y ∈ M q := by
    intro q hq r y hy
    rw [hMN q hq] at hy ⊢
    exact mem_locSub.1 ((locSub q hq.isPrime (N q)).smul_mem r (mem_locSub.2 hy))
  have hMsat : ∀ q : Ideal R, q.IsMaximal → ∀ (u : R) (y : V), u ∉ q → u • y ∈ M q → y ∈ M q := by
    intro q hq u y hu h
    rw [hMN q hq] at h ⊢
    exact mem_loc_of_smul hq.isPrime hu h
  let L : Submodule R V := ⨅ q : {q : Ideal R // q.IsMaximal}, locSub q.1 q.2.isPrime (N q.1)
  have hL : ∀ x, x ∈ L ↔ ∀ q : Ideal R, q.IsMaximal → x ∈ M q := by
    intro x
    simp only [L, Submodule.mem_iInf, mem_locSub]
    constructor
    · intro h q hq
      rw [hMN q hq]
      exact h ⟨q, hq⟩
    · intro h q
      rw [← hMN q.1 q.2]
      exact h q.1 q.2
  obtain ⟨c1, hc1, hc1N⟩ := commonMult (fun (q : Ideal R) (c : R) => ∀ y ∈ N q, c • y ∈ L0)
    (fun q c d h y hy => by rw [mul_smul]; exact L0.smul_mem d (h y hy)) hfin.toFinset
    (fun q hq => by
      have hq' : q.IsMaximal ∧ M q ≠ loc q L0 := (Set.Finite.mem_toFinset hfin).1 hq
      obtain ⟨hfg, _⟩ := hNfull q hq'.1
      exact exists_smul_le (K := K) hfg hL0sp)
  obtain ⟨c2, hc2, hc2N⟩ := commonMult (fun (q : Ideal R) (c : R) => ∀ y ∈ L0, c • y ∈ N q)
    (fun q c d h y hy => by rw [mul_smul]; exact (N q).smul_mem d (h y hy)) hfin.toFinset
    (fun q hq => by
      have hq' : q.IsMaximal ∧ M q ≠ loc q L0 := (Set.Finite.mem_toFinset hfin).1 hq
      obtain ⟨_, hsp⟩ := hNfull q hq'.1
      exact exists_smul_le (K := K) hL0fg hsp)
  have hLc1 : ∀ x ∈ L, c1 • x ∈ L0 := by
    intro x hx
    apply mem_of_forall_loc
    intro q hq
    have hxq := (hL x).1 hx q hq
    by_cases hqS : M q = loc q L0
    · rw [hqS] at hxq
      exact mem_locSub.1 ((locSub q hq.isPrime L0).smul_mem c1 (mem_locSub.2 hxq))
    · rw [hMN q hq] at hxq
      obtain ⟨s, hs, hsx⟩ := mem_loc.1 hxq
      refine mem_loc.2 ⟨s, hs, ?_⟩
      rw [smul_comm]
      exact hc1N q ((Set.Finite.mem_toFinset hfin).2 ⟨hq, hqS⟩) _ hsx
  have hLc2 : ∀ y ∈ L0, c2 • y ∈ L := by
    intro y hy
    rw [hL]
    intro q hq
    by_cases hqS : M q = loc q L0
    · rw [hqS]
      exact mem_loc_of_mem hq.ne_top (L0.smul_mem c2 hy)
    · rw [hMN q hq]
      exact mem_loc_of_mem hq.ne_top (hc2N q ((Set.Finite.mem_toFinset hfin).2 ⟨hq, hqS⟩) y hy)
  have hLfg : L.FG := by
    let f : V →ₗ[R] V := c1 • LinearMap.id
    have hK1 : algebraMap R K c1 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc1
    have hf : Function.Injective f := fun v w h => by
      have h' : c1 • v = c1 • w := by simpa only [f, LinearMap.smul_apply, LinearMap.id_apply] using h
      have h'' : algebraMap R K c1 • v = algebraMap R K c1 • w := by
        rw [algebraMap_smul, algebraMap_smul]; exact h'
      exact (smul_right_inj hK1).1 h''
    refine Submodule.fg_of_fg_map_injective (f := f) hf ?_
    refine Submodule.FG.of_le hL0fg ?_
    rintro _ ⟨x, hx, rfl⟩
    simpa [f] using hLc1 x hx
  have hLspan : Submodule.span K (L : Set V) = ⊤ := by
    rw [eq_top_iff, ← hL0sp, Submodule.span_le]
    intro y hy
    have hK : algebraMap R K c2 ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hc2
    have h1 : c2 • y ∈ Submodule.span K (L : Set V) := Submodule.subset_span (hLc2 y hy)
    have h2 := Submodule.smul_mem _ (algebraMap R K c2)⁻¹ h1
    rwa [← algebraMap_smul K c2 y, inv_smul_smul₀ hK] at h2
  have hLfull : IsFullLat K L := by
    unfold IsFullLat
    exact ⟨hLfg, hLspan⟩
  have hloc : ∀ p : Ideal R, p.IsMaximal → loc p L = M p := by
    intro p hp
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hsx⟩ := mem_loc.1 hx
      exact hMsat p hp s x hs ((hL _).1 hsx p hp)
    · intro hx
      obtain ⟨d, hd, hdx⟩ := exists_smul_mem (K := K) L (v := x) (by rw [hLspan]; exact Submodule.mem_top)
      obtain ⟨s, hs, hsx⟩ := exists_smul_mem_of_local M L hL hMsmul hMsat hp hx hd hdx
      exact mem_loc.2 ⟨s, hs, hsx⟩
  refine ExistsUnique.intro L ⟨hLfull, hloc⟩ ?_
  rintro L' ⟨_, hloc'⟩
  ext x
  constructor
  · intro hx
    rw [hL]
    intro q hq
    rw [← hloc' q hq]
    exact mem_loc_of_mem hq.ne_top hx
  · intro hx
    apply mem_of_forall_loc L' x
    intro q hq
    rw [hloc' q hq]
    exact (hL x).1 hx q hq
end PI.LatLocGlob.Proof
