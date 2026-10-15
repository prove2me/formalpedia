-- Prove2me | solution 1 for TaoFivePrimes.rh_high_height_dirichlet_guards
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-15T05:49:57.66589+00:00
-- url     : https://prove2.me/submissions/872327a4-b62d-41f4-a040-088e8533d4e9

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighDirichletArithmetic
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic00
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic01
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic02
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic03
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic04
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic05
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic06
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic07
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic08
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic09
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic10
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic11
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic12
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic13
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic14
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic15
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic16
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic17
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic18
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic19
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic20
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic21
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic22
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic23
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic24
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic25
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic26
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic27
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic28
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic29
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic30
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic31
import Theorems.Thm_TaoFivePrimes_rh_high_height_dirichlet_arithmetic32
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000
set_option backward.isDefEq.respectTransparency false
theorem solution :
  ∀ n:Nat,1 ≤ n ∧ n≤50000 →
  RHHighDirichletArithmetic.guard n (RHHighDirichletArithmetic.compute n)=true ∧
  2*(RHHighDirichletArithmetic.delta n).natAbs+2^100≤RHHighLogData.D ∧
  RHHighDirichletArithmetic.bin n≤928 := by
  intro n hn
  let b:=(n-1)/1536
  let c:=((n-1)%1536)/16
  let j:=(n-1)%16
  have hb:b<33:=by dsimp [b];omega
  have hc:c<96:=by dsimp [c];omega
  have hj:j<16:=by dsimp [j];omega
  have he:1536*b+1+16*c+j=n:=by dsimp [b,c,j];omega
  interval_cases b
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic00 c hc' j hj
    have he':1+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic01 c hc' j hj
    have he':1537+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic02 c hc' j hj
    have he':3073+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic03 c hc' j hj
    have he':4609+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic04 c hc' j hj
    have he':6145+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic05 c hc' j hj
    have he':7681+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic06 c hc' j hj
    have he':9217+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic07 c hc' j hj
    have he':10753+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic08 c hc' j hj
    have he':12289+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic09 c hc' j hj
    have he':13825+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic10 c hc' j hj
    have he':15361+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic11 c hc' j hj
    have he':16897+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic12 c hc' j hj
    have he':18433+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic13 c hc' j hj
    have he':19969+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic14 c hc' j hj
    have he':21505+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic15 c hc' j hj
    have he':23041+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic16 c hc' j hj
    have he':24577+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic17 c hc' j hj
    have he':26113+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic18 c hc' j hj
    have he':27649+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic19 c hc' j hj
    have he':29185+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic20 c hc' j hj
    have he':30721+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic21 c hc' j hj
    have he':32257+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic22 c hc' j hj
    have he':33793+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic23 c hc' j hj
    have he':35329+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic24 c hc' j hj
    have he':36865+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic25 c hc' j hj
    have he':38401+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic26 c hc' j hj
    have he':39937+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic27 c hc' j hj
    have he':41473+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic28 c hc' j hj
    have he':43009+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic29 c hc' j hj
    have he':44545+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic30 c hc' j hj
    have he':46081+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<96:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic31 c hc' j hj
    have he':47617+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  · have hc':c<53:=by omega
    have h:=TaoFivePrimes.rh_high_height_dirichlet_arithmetic32 c hc' j hj
    have he':49153+16*c+j=n:=by omega
    rw [he'] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
