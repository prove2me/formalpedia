-- Prove2me | solution 1 for StableMSR.Recovery.RegionalBallDP.decode_regional_menus
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-21T13:13:53.627177+00:00
-- url     : https://prove2.me/submissions/922c3ff8-cdbc-4856-9407-2ec57bb58c3e

import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_regional_table_machine
import Theorems.Thm_StableMSR_Recovery_RegionalBallDP_regional_relaxation_optimal
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
theorem solution :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0<x.k → 0<x.n → shape x → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤p.eval x.cap ∧
      let y:=worldOf x.k x.rows x.dist t
      Ready y t ∧ endpoints y ∧ ∀v,vertex x v → InTable x v → ∀u,Route x v u →
        good y v ∧ score y v≤weight x x.k u := by
  obtain ⟨p,cmd,run⟩:=regional_table_machine
  refine ⟨p,cmd,?_⟩
  intro x s hk hn hs rd
  have hH : 0<x.rows := by have h:=hs.2;omega
  obtain ⟨t,z,ez,tz,rt,h,a,b,c⟩:=run x s hk hH rd
  let y:=worldOf x.k x.rows x.dist t
  obtain ⟨ep,opt⟩:=regional_relaxation_optimal x hk hn hs h a b y.mem c
  refine ⟨t,z,ez,tz,rt,ep,?_⟩
  intro v hv cert u hu
  obtain ⟨path,le⟩:=opt v hv u hu
  change Route x v (word y v) at path
  change weight x (width x v) (word y v)≤weight x (width x v) u at le
  have cover:=cert.2.2 _ path
  have wd:=cert.2.1
  have ht (j : ℕ) (hj : j<x.k) (w : Bool) : word y v j w=field y v j w := if_pos hj
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro j hj l hl e
    exact cover.1 j hj l hl (by rw [ht j hj false,ht l hl false];exact e)
  · intro i hi
    obtain ⟨j,hj,hit⟩:=cover.2 i hi
    refine ⟨j,hj,?_⟩
    rw [ht j hj false,ht j hj true] at hit
    exact hit
  · rw [wd] at le
    have eq : score y v=weight x x.k (word y v) := by
      apply Finset.sum_congr rfl
      intro j jh
      have hj : j<x.k:=Finset.mem_range.mp jh
      rw [if_pos hj,ht j hj false,ht j hj true];rfl
    rwa [eq]

