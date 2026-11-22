-- Prove2me | solution 1 for StableMSR.Recovery.WindowJoins.join_outputs_are_profiles
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-22T22:49:11.965513+00:00
-- url     : https://prove2.me/submissions/4c309e60-7f96-4b10-a9a4-6b820d5e0db4

import Theorems.Thm_StableMSR_Recovery_WindowJoins_derived_endpoint_bounds
import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
theorem solution (x : World) (e : ℚ) (H : ℕ) (m out : Mem) (hn : 0< x.n) (hk : 0< x.k)
    (cert : Encodes x e {x with rows:=H,mem:=m})
    (ok : let y:={x with rows:=H,mem:=m};let z:={y with mem:=out};let g:=decode y
          ∀r< g.size,g.goal r< g.size → RowOK y g (g.goal r) (0≤ center z r 0) (word z r)) :
    Profiles x e out := by
  let y:={x with rows:=H,mem:=m};let z:={y with mem:=out};let g:=decode y
  have sane : Sane y g:=by
    refine ⟨fun v=>min_le_left ..,?_⟩;intro q j w;change 0≤ legalize x.n _ ∧ legalize x.n _<(x.n:ℤ)
    unfold legalize;split
    · assumption
    · omega
  intro u hu i hi
  let W:=piece x u i
  have info (c : ℕ) (hc : c≤ x.k) := cert.targets u hu i hi c hc
  let idx:=fun c=>index x.n u i c
  let T:=fun c=>word z (idx c)
  have state (c : ℕ) (hc : c≤ x.k) : RowOK y g (g.goal (idx c)) (0≤ center z (idx c) 0) (T c):=
    ok _ (info c hc).1 (info c hc).2.1
  have agree {c} (hc : c≤ x.k) (on : 0≤ center z (idx c) 0) (j : ℕ) (hj : j< c) (w : Bool) :
      token (replace x out) u i c j w=T c j w:=by
    have legal:=(derived_endpoint_bounds y g sane hn _ _ ((state c hc).1 on)).1 j w
    have lt : j< x.k:=hj.trans_le hc
    have eq : T c j w=field z (idx c) j w:=if_pos lt
    rw [eq] at legal ⊢;exact if_pos legal
  constructor
  · intro c hc on;have d:=(state c hc).1 on;obtain ⟨owns,_,_⟩:=(info c hc).2.2.2
    obtain ⟨centers,distinct,cov⟩:=owns _ d
    refine ⟨?_,?_,?_⟩
    · intro j hj;rw [agree hc on j hj false];exact centers _ hj
    · intro j hj l hl eq;rw [agree hc on j hj false,agree hc on l hl false] at eq;exact distinct j hj l hl eq
    · intro p hp;obtain ⟨j,hj,hit⟩:=cov p hp;refine ⟨j,hj,?_⟩
      unfold contains RegionalBallDP.containsPoint at hit ⊢;rw [agree hc on j hj false,agree hc on j hj true];exact hit
  constructor
  · intro unused;obtain ⟨w,d⟩:=(info 0 (by omega)).2.2.2.2.1 unused rfl
    exact ((state 0 (by omega)).2 _ d).1
  · intro used pos tw P validP;dsimp only;intro hc
    let c:=number x (piece x u i) (scale x u) P
    obtain ⟨w,d,cheap⟩:=(info c hc).2.2.2.2.2 used pos tw P validP rfl
    obtain ⟨on,le⟩:=(state c hc).2 _ d
    have len:= (info c hc).2.2.1
    change g.len (g.goal (idx c))=c at len;rw [len] at le
    refine ⟨on,le_trans ?_ (le.trans cheap)⟩;apply le_of_eq
    unfold weight;apply Finset.sum_congr rfl;intro j hj;by_cases sm : j< c
    · rw [if_pos sm,if_pos sm,agree hc on j sm false,agree hc on j sm true]
    · rw [if_neg sm,if_neg sm]
