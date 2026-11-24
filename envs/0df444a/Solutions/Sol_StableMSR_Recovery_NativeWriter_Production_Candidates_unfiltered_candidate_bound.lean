-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.unfiltered_candidate_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:39:34.939356+00:00
-- url     : https://prove2.me/submissions/61cbc788-8449-49cc-9471-bd06a3c1d795

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000
namespace StableMSR.Recovery.TightLanguage
open SingleCircuit
set_option autoImplicit false

theorem flat_length {I O : Type} (xs : List I) (f : I → List O) (B : ℕ)
    (h : ∀ i, i ∈ xs → (f i).length ≤ B) : (xs.flatMap f).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    have a := h i (by simp)
    have b := ih (fun j hj => h j (by simp [hj]))
    omega

theorem assignments_bound (d : Instance) (K : ℕ) (hK : ∀ v, (d.menu v).length ≤ K) (s : List ℕ) :
    (assignments d s).length ≤ K^s.length := by
  induction s with
  | nil => simp [assignments]
  | cons v s ih =>
    unfold assignments
    apply Nat.le_trans (flat_length _ _ (K^s.length) (fun x _ => by simpa using ih))
    simpa [Nat.pow_succ,Nat.mul_comm] using Nat.mul_le_mul_right (K^s.length) (hK v)

theorem cut_size (vs : List ℕ) (w : ℕ) (s : List ℕ) (h : s ∈ cuts vs w) : s.length ≤ w := by
  induction vs generalizing w s with
  | nil => simp [cuts] at h; simp [h]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts] at h; simp [h]
    | succ w =>
      rw [cuts,List.mem_append] at h
      rcases h with h | h
      · exact ih _ _ h
      · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
        simpa using ih _ _ ht

theorem cuts_count (vs : List ℕ) (w : ℕ) : (cuts vs w).length ≤ (vs.length+1)^w := by
  induction vs generalizing w with
  | nil => simp [cuts]
  | cons v vs ih =>
    cases w with
    | zero => simp [cuts]
    | succ w =>
      rw [cuts,List.length_append,List.length_map,List.length_cons]
      calc
        _ ≤ (vs.length+1)^(w+1) + (vs.length+1)^w := Nat.add_le_add (ih _) (ih _)
        _ = (vs.length+1)^w * (vs.length+1+1) := by simp only [Nat.pow_succ,Nat.mul_succ]
        _ ≤ _ := by rw [Nat.pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)

theorem parts_count (d : Instance) (allowed : List ℕ) : (parts d allowed).length ≤ allowed.length :=
  List.length_filterMap_le .. 

def gateEnvelope (N M B w : ℕ) := 2+N*((N+1)^w*(N*M^w)*((N*M)*(2*B+N+2)))+N

def menuLimit (n h : ℕ) := (h+1)*n^(2*(h+1))

theorem envelope_power (n h w : ℕ) (hn:2≤n) :
    gateEnvelope n (menuLimit n h) n w ≤ n^(15*((h+1)*(w+1))) := by
  let p:=(h+1)*(w+1)
  let A:=n^p
  have h1:1≤h+1:=by omega
  have w1:1≤w+1:=by omega
  have hw:h+1≤p:=Nat.le_mul_of_pos_right _ w1
  have wp:w≤p:=by have e:=Nat.le_mul_of_pos_left (w+1) h1;omega
  have pp:1≤p:=h1.trans hw
  have na:n≤A:=by simpa [A] using (Nat.pow_le_pow_right (show 1≤n by omega) pp)
  have aa:2≤A:=hn.trans na
  have k: menuLimit n h≤n^(3*(h+1)) := by
    have hh:h+1≤n^(h+1):=(Nat.le_of_lt (Nat.lt_two_pow_self (n:=h+1))).trans (Nat.pow_le_pow_left hn _)
    calc _ ≤ n^(h+1)*n^(2*(h+1)) := Nat.mul_le_mul_right _ hh
         _ = _ := by rw [←pow_add];congr 1;omega
  have kw:(menuLimit n h)^w≤A^3 := by
    apply (Nat.pow_le_pow_left k w).trans
    rw [←pow_mul,show A^3=n^(p*3) from (pow_mul ..).symm]
    apply Nat.pow_le_pow_right (by omega)
    dsimp [p];nlinarith
  have k0:menuLimit n h≤A^3:=by
    apply k.trans
    rw [show A^3=n^(p*3) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have nw:(n+1)^w≤A^2 := by
    have plus:n+1≤n^2:=by nlinarith [Nat.mul_le_mul_right n hn]
    apply (Nat.pow_le_pow_left plus w).trans
    rw [←pow_mul,show A^2=n^(p*2) from (pow_mul ..).symm]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have three:2*n+n+2≤A^3 := by
    have sq:2*A≤A*A:=Nat.mul_le_mul_right A aa
    have cube:2*(A*A)≤A*(A*A):=Nat.mul_le_mul_right _ aa
    nlinarith
  have big:n*((n+1)^w*(n*(menuLimit n h)^w)*((n*menuLimit n h)*(2*n+n+2)))≤A^14 := by
    calc _ ≤ A*(A^2*(A*A^3)*((A*A^3)*A^3)) := Nat.mul_le_mul na (Nat.mul_le_mul
              (Nat.mul_le_mul nw (Nat.mul_le_mul na kw)) (Nat.mul_le_mul (Nat.mul_le_mul na k0) three))
         _ = _ := by ring
  have rest:2+n≤A^14 := by
    apply (show 2+n≤A^2 by nlinarith [Nat.mul_le_mul_right A aa]).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  change 2+_+n≤_
  calc _ ≤ A^14+A^14 := by omega
       _ = 2*A^14 := by omega
       _ ≤ A*A^14 := Nat.mul_le_mul_right _ aa
       _ = A^15 := by ring
       _ = n^(15*p) := by rw [show A^15=n^(p*15) from (pow_mul ..).symm,Nat.mul_comm p]
end StableMSR.Recovery.TightLanguage
namespace StableMSR.Recovery.NativeWriter.Production.Candidates
open SingleCircuit SingleCodes TightLanguage OracleQueries WindowCSP
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1400000

theorem tape_envelope (enc:Key→ℕ) (d:Instance) (w K B:ℕ) (hn:0<d.n) (hk:0<K)
    (menu:∀v,(d.menu v).length≤K) (mask:∀v x,(d.owned v x).length≤B) :
    (tape enc d w).length≤gateEnvelope d.n K B w := by
  let vs:=vertices d
  let cuts' := cuts vs (min w d.n)
  let F:=d.n*K*(2*B+d.n+2)
  have nv:vs.length≤d.n:=(List.length_filter_le ..).trans (by simp)
  have nc:cuts'.length≤(d.n+1)^w:=(cuts_count vs _).trans ((Nat.pow_le_pow_left (by omega:vs.length+1≤d.n+1) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.min_le_left ..)))
  have nc' (s:List ℕ) : (keysFor d vs s).length≤d.n:=(parts_count d _).trans ((List.length_filter_le ..).trans nv)
  have tr (c:List ℕ) (a:Assignment) (v x:ℕ) (hc:c.length≤d.n) :
      (trial enc d c a v x).length≤B+d.n+1:=by
    have n: (children d c v ((v,x)::a)).length≤d.n:=by
      simpa only [children,List.length_map] using (parts_count d (c.erase v)).trans ((List.length_erase_le ..).trans hc)
    have m:=mask v x
    simp only [trial,List.length_append,List.length_map,List.length_singleton];omega
  have row (c:List ℕ) (a:Assignment) (hc:c.length≤d.n) : (entry enc d c a).length≤F:=by
    have per (v:ℕ) : ((d.menu v).flatMap (trial enc d c a v)).length≤K*(B+d.n+1) :=
      (flat_length _ _ _ (fun x _=>tr c a v x hc)).trans (Nat.mul_le_mul_right _ (menu v))
    have all: (c.flatMap (fun v=>(d.menu v).flatMap (trial enc d c a v))).length≤d.n*(K*(B+d.n+1)) :=
      (flat_length _ _ _ (fun v _=>per v)).trans (Nat.mul_le_mul_right _ hc)
    have pos:1≤d.n*K:=Nat.mul_pos hn hk
    simp only [entry,List.length_append,List.length_singleton];dsimp [F]
    rw [←Nat.mul_assoc] at all;nlinarith [Nat.zero_le (d.n*K*B)]
  have visitL (k:ℕ) (s c:List ℕ) (hs:s.length≤w) (h:k<d.n) :
      (visitTape enc d k s c).length≤K^w*F:=by
    unfold visitTape;split
    · next yes=>
        have len:c.length=k+1:=by simp only [Bool.and_eq_true,beq_iff_eq] at yes;exact yes.1
        apply (flat_length _ _ F (fun a _=>row c a (by omega))).trans
        exact Nat.mul_le_mul_right F ((assignments_bound d K menu s).trans (Nat.pow_le_pow_right hk hs))
    · simp
  have component (k:ℕ) (s:List ℕ) (h:k<d.n) (hs:s∈cuts') :
      ((keysFor d vs s).flatMap (visitTape enc d k s)).length≤d.n*(K^w*F):=
    (flat_length _ _ _ (fun c _=>visitL k s c ((cut_size vs _ s hs).trans (Nat.min_le_left ..)) h)).trans
      (Nat.mul_le_mul_right _ (nc' s))
  have cutRow (k:ℕ) (h:k<d.n) : (cuts'.flatMap (fun s=>(keysFor d vs s).flatMap (visitTape enc d k s))).length≤
      (d.n+1)^w*(d.n*(K^w*F)):=
    (flat_length _ _ _ (fun s hs=>component k s h hs)).trans (Nat.mul_le_mul_right _ nc)
  have rows : (rowTape enc d w).length≤d.n*((d.n+1)^w*(d.n*(K^w*F))):=by
    simpa only [rowTape,vs,cuts',List.length_range] using
      (flat_length (List.range d.n) (fun k=>cuts'.flatMap (fun s=>(keysFor d vs s).flatMap (visitTape enc d k s))) _
        (fun k h=>cutRow k (List.mem_range.mp h)))
  have nroot: (parts d vs).length≤d.n := (parts_count d vs).trans nv
  simp only [tape,List.length_append,List.length_map,List.length_singleton,gateEnvelope]
  change (rowTape enc d w).length+(parts d vs).length+1≤_
  simp only [Nat.mul_assoc] at rows ⊢
  dsimp [F] at rows
  simp only [Nat.mul_assoc] at rows
  omega

theorem scene_envelope (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) (enc:Key→ℕ) (hn:1≤x.n) :
    (tape enc (instanceOf x W R h) w).length≤gateEnvelope x.n (menuLimit x.n h) x.n w := by
  let K := menuLimit x.n h
  have pos : 0<K := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have words : (SingleCodes.words x.n h).length ≤ K := by
    apply (flat_length _ _ (CartesianBallRows.rows x.n (h+1)) ?_).trans
    · simp [K,menuLimit,CartesianBallRows.rows]
    · intro a ha; simp
  apply tape_envelope enc (instanceOf x W R h) w K x.n hn pos
  · intro v
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · exact (List.length_filter_le ..).trans words
    · simp
  · intro v a
    simp only [SingleCodes.instanceOf,SingleCodes.lookup]
    split
    · simp only [blockList,List.length_map,Finset.length_toList]
      apply (Finset.card_filter_le ..).trans
      apply Finset.card_image_le.trans
      simpa using (Finset.card_le_univ (WindowCSP.window x.dist W R ⟨v,by assumption⟩))
    · simp


theorem regional_bound (x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    (tape enc (instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ))) (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ)) := by
  have realPos:0<(e:ℝ):=by exact_mod_cast he
  have realLt:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ) := by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ realPos).2 (by linarith)
  apply (scene_envelope x _ _ _ _ enc (by omega)).trans
  apply (envelope_power _ _ _ hn).trans
  apply Nat.pow_le_pow_right (by omega)
  have b:WindowCSP.budget (e:ℝ)+1≤5*ownerBound (e:ℝ):=by unfold WindowCSP.budget;omega
  have c:=Nat.mul_le_mul_right (widthBound (e:ℝ)+1) b
  unfold parameterEnvelope
  nlinarith
end StableMSR.Recovery.NativeWriter.Production.Candidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates
theorem solution
    (x:World) (u i:ℕ) (e:ℚ) (enc:Key→ℕ) (he:0<e) (hl:e<1) (hn:2≤x.n) :
    let d:=SingleCodes.instanceOf x (WindowProfiles.piece x u i) (scale x u) (budget (e:ℝ))
    (tape enc d (widthBound (e:ℝ))).length≤x.n^(75*parameterEnvelope (e:ℝ)) := regional_bound x u i e enc he hl hn
