-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.integer_instance_exact
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T00:18:33.009547+00:00
-- url     : https://prove2.me/submissions/63b3a8aa-46bd-4003-ae20-c8e38713fb26

import Definitions.Def_StableMSR_IntegerRegionalGeometry
set_option linter.all false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem samples_len (x:World) : (samples x).length=x.n*x.n:=by
  have calcLen (ls:List (Fin x.n)) :
      (ls.flatMap (fun a=>(List.finRange x.n).map (x.dist a))).length=ls.length*x.n:=by
    induction ls with
    | nil=>simp
    | cons a ls ih=>simp [ih,Nat.succ_mul,Nat.add_comm]
  simpa [samples] using calcLen (List.finRange x.n)

theorem sampled (x:World) (a b:Fin x.n) : x.dist a b∈samples x :=
  List.mem_flatMap.mpr ⟨a,by simp,List.mem_map.mpr ⟨b,by simp,rfl⟩⟩

theorem rank_mono (ds:List ℝ) {a b:ℝ} (h:a≤b) : rank ds a≤rank ds b:=by
  induction ds with
  | nil=>simp [rank]
  | cons z zs ih=>
    by_cases za:z<a
    · have zb:z<b:=lt_of_lt_of_le za h
      simpa [rank,List.filter_cons,za,zb] using ih
    · by_cases zb:z<b <;> simp [rank,List.filter_cons,za,zb] at ih ⊢ <;> omega

theorem rank_strict (ds:List ℝ) {a b:ℝ} (ha:a∈ds) (h:a<b) : rank ds a<rank ds b:=by
  induction ds with
  | nil=>simp at ha
  | cons z zs ih=>
    rcases List.mem_cons.mp ha with rfl|old
    · have m:=rank_mono zs h.le
      simp [rank,List.filter_cons,h] at m ⊢;omega
    · have m:=ih old
      by_cases za:z<a
      · have zb:z<b:=lt_trans za h
        simpa [rank,List.filter_cons,za,zb] using m
      · by_cases zb:z<b <;> simp [rank,List.filter_cons,za,zb] at m ⊢ <;> omega

theorem rank_cap (x:World) (v:ℝ) : rank (samples x) v<unit x.n:=by
  have h:=List.length_filter_le (fun z=>decide (z<v)) (samples x);rw [samples_len] at h;unfold rank unit;omega

theorem band_mono (R:ℝ) {a b:ℝ} (h:a≤b) : band R a≤band R b:=by
  unfold band;split_ifs <;> first | decide | linarith

theorem scalar_lt (x:World) (R:ℝ) {a b:ℝ} (ha:a∈samples x) (h:a<b) :
    scalar x.n (samples x) R a<scalar x.n (samples x) R b :=
  Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ (band_mono R h.le)) (rank_strict _ ha h)

theorem scalar_order (x:World) (R:ℝ) {a b:ℝ} (hb:b∈samples x) :
    scalar x.n (samples x) R a ≤ scalar x.n (samples x) R b ↔ a≤b := by
  constructor
  · intro h;by_contra no;exact (Nat.not_lt_of_ge h) (scalar_lt x R hb (lt_of_not_ge no))
  · intro h;exact Nat.add_le_add (Nat.mul_le_mul_right _ (band_mono R h)) (rank_mono _ h)

theorem scalar_limits (x:World) (R v:ℝ) (pos:0<R) :
    let S:=scalar x.n (samples x) R v;let H:=unit x.n
    (S≤2*H ↔ v≤2*R) ∧ (S≤4*H ↔ v≤4*R) ∧ (S≤8*H ↔ v≤8*R) ∧ S<10*H := by
  have rk:=rank_cap x v
  dsimp only;unfold scalar band
  split_ifs with h2 h4 h8
  · have h4:v≤4*R:=by linarith
    have h8:v≤8*R:=by linarith
    simp only [h2,h4,h8,iff_true];omega
  · have h8:v≤8*R:=by linarith
    simp only [h2,h4,h8,iff_false,iff_true];omega
  · simp only [h2,h4,h8,iff_false,iff_true];omega
  · simp only [h2,h4,h8,iff_false];omega

theorem metric_nonneg {x:World} (hm:IsMetricArray x.dist) (a b:Fin x.n) : 0≤x.dist a b:=by
  obtain ⟨metric,eq⟩:=hm;letI:=metric;rw [←eq a b];exact dist_nonneg
theorem metric_zero {x:World} (hm:IsMetricArray x.dist) (a:Fin x.n) : x.dist a a=0:=by
  obtain ⟨metric,eq⟩:=hm;letI:=metric;rw [←eq a a];exact dist_self _
theorem scalar_zero (x:World) (R:ℝ) (pos:0<R) (hm:IsMetricArray x.dist) : scalar x.n (samples x) R 0=0:=by
  have nonneg:∀z∈samples x,0≤z:=by
    intro z hz;obtain ⟨a,_,hb⟩:=List.mem_flatMap.mp hz;obtain ⟨b,_,rfl⟩:=List.mem_map.mp hb;exact metric_nonneg hm a b
  have eq:((samples x).filter (fun z=>decide (z<0)))=[]:=List.filter_eq_nil_iff.mpr (fun z hz=>by simp [not_lt.mpr (nonneg z hz)])
  simp [scalar,band,show (0:ℝ)≤2*R by linarith,rank,eq]

theorem Prepared.bounded {x:World} {R:ℝ} {m:ℤ→ℤ} (t:Prepared x R m) (h:0<R) : Bounded x.n m:=by
  intro a b;rw [t a b];exact ⟨by positivity,by exact_mod_cast (scalar_limits x R (x.dist a b) h).2.2.2⟩

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open Compiler OracleQueries WindowCSP SingleCircuit Supplement
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem Prepared.oracle {x:World} {R:ℝ} {m:ℤ→ℤ} (t:Prepared x R m) (pos:0<R) (metric:IsMetricArray x.dist) (a b:ℤ) :
    MinSumFPT.oracleAnswer (matrix x m).dist a b=(scalar x.n (samples x) R (MinSumFPT.oracleAnswer x.dist a b):ℝ) := by
  simp only [MinSumFPT.oracleAnswer,matrix]
  cases ha:MinSumFPT.toPoint x.n a <;> cases hb:MinSumFPT.toPoint x.n b <;> simp [scalar_zero x R pos metric] <;> exact_mod_cast t _ _

theorem sampled_oracle (x:World) (hn:0<x.n) (metric:IsMetricArray x.dist) (a b:ℤ) :
    MinSumFPT.oracleAnswer x.dist a b∈samples x:=by
  have zero:(0:ℝ)∈samples x:=by let z:Fin x.n:=⟨0,hn⟩;simpa [metric_zero metric z] using sampled x z z
  unfold MinSumFPT.oracleAnswer
  cases MinSumFPT.toPoint x.n a <;> cases MinSumFPT.toPoint x.n b <;> first | exact zero | apply sampled

theorem equivalent (n k rows h:ℕ) (origin:ℕ→ℤ) (f g:Fin n→Fin n→ℝ) (S R:ℝ) (W:Cluster n)
    (cmp:∀a b c e:ℤ,MinSumFPT.oracleAnswer f a b ≤ MinSumFPT.oracleAnswer f c e ↔
        MinSumFPT.oracleAnswer g a b ≤ MinSumFPT.oracleAnswer g c e)
    (near:∀a b,f a b≤2*S ↔ g a b≤2*R) (mid:∀a b,f a b≤4*S ↔ g a b≤4*R)
    (wide:∀a b,f a b≤8*S ↔ g a b≤8*R) :
    SingleCodes.instanceOf ⟨n,k,rows,f,origin⟩ W S h=SingleCodes.instanceOf ⟨n,k,rows,g,origin⟩ W R h := by
  have far (a b:Fin n) : 2*S<f a b ↔ 2*R<g a b:=by simpa only [not_le] using not_congr (near a b)
  have net:greedyNet f S W=greedyNet g R W:=by simp only [greedyNet,far]
  have owner:anchor f W S=anchor g W R:=by funext p;simp only [anchor,net,near]
  have win (v:Fin n) : window f W S v=window g W R v:=by simp only [window,ball,mid]
  let X:=fun d:Fin n→Fin n→ℝ=>(⟨n,k,rows,d,origin⟩:World)
  have rel (z u:ℕ) : FewBallRows.digitRel (RegionalSeeds.seedWorld (X f) h) z u=FewBallRows.digitRel (RegionalSeeds.seedWorld (X g) h) z u:=by
    funext a b;apply propext
    simp only [FewBallRows.digitRel,FewBallRows.joined,FewBallRows.distAt,RegionalSeeds.seedWorld,X,cmp]
  have decode (U:Cluster n) (c:ℕ) : SingleCodes.decode (X f) U h c=SingleCodes.decode (X g) U h c:=by
    simp only [SingleCodes.decode,rel] <;> rfl
  have menu (U:Cluster n) : SingleCodes.menu (X f) U h=SingleCodes.menu (X g) U h:=by
    simp only [SingleCodes.menu,decode];rfl
  dsimp only [X] at decode menu
  simp only [SingleCodes.instanceOf,net,win,menu,decode,owner,wide]

theorem instance_exact (x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) (m:ℤ→ℤ)
    (hn:0<x.n) (pos:0<R) (metric:IsMetricArray x.dist) (t:Prepared x R m) :
    SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h=SingleCodes.instanceOf x W R h := by
  apply equivalent
  · intro a b c e
    change MinSumFPT.oracleAnswer (matrix x m).dist a b ≤ MinSumFPT.oracleAnswer (matrix x m).dist c e ↔ _
    rw [t.oracle pos metric a b,t.oracle pos metric c e,Nat.cast_le];exact scalar_order x R (sampled_oracle x hn metric c e)
  all_goals intro a b
  all_goals change (m (address a b):ℝ)≤_ ↔ _
  all_goals rw [t a b];norm_cast
  · exact (scalar_limits x R (x.dist a b) pos).1
  · exact (scalar_limits x R (x.dist a b) pos).2.1
  · exact (scalar_limits x R (x.dist a b) pos).2.2.1

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
theorem solution (x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) (m:ℤ→ℤ)
    (hn:0<x.n) (pos:0<R) (metric:IsMetricArray x.dist) (t:Prepared x R m) :
    SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h=SingleCodes.instanceOf x W R h ∧ Bounded x.n m := ⟨instance_exact x W R h m hn pos metric t,t.bounded pos⟩
