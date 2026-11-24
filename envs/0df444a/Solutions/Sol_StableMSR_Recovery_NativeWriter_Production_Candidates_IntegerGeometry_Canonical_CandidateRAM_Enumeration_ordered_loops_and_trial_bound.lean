-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration.ordered_loops_and_trial_bound
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:37:06.748436+00:00
-- url     : https://prove2.me/submissions/2cb73501-cb26-4be8-8ae1-7b67361d856a

import Definitions.Def_StableMSR_SeparatorLoopOrder
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open SingleCircuit TightLanguage WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 2300000

theorem preorder_exact (vs:List ℕ) (w:ℕ) : preorder vs w=TightLanguage.cuts vs w:=by
  induction w generalizing vs with
  | zero=>cases vs <;> rfl
  | succ w ih=>
    induction vs with
    | nil=>rfl
    | cons v vs iv=>
      calc
        preorder (v::vs) (w+1) = preorder vs (w+1) ++ (preorder vs w).map (v::·) := by
          simp [preorder,extensions,List.flatMap_append]
        _ = _ := by rw [iv,ih];rfl

def products (menu:ℕ→List ℕ) : List ℕ→List Assignment
  | []=>[[]] | v::vs=>(menu v).flatMap fun x=>(products menu vs).map ((v,x)::·)

theorem snoc_products (menu:ℕ→List ℕ) (vs:List ℕ) (last:ℕ) :
    products menu (vs++[last])=(products menu vs).flatMap fun a=>(menu last).map (fun x=>a++[(last,x)]) := by
  induction vs with
  | nil=>simp [products, List.flatMap_map, ←List.map_eq_flatMap]
  | cons v vs ih=>
    simp [products,ih,List.flatMap_assoc,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

theorem range_blocks {A:Type} (f:ℕ→ℕ→A) (N M:ℕ) (hm:0<M) :
    (List.range (N*M)).map (fun k=>f (k/M) (k%M))=
      (List.range N).flatMap fun q=>(List.range M).map (fun r=>f q r) :=by
  induction N with
  | zero=>simp
  | succ n ih=>
    rw [Nat.succ_mul,List.range_add,List.map_append,ih,List.range_succ,List.flatMap_append]
    simp only [List.flatMap_singleton,List.map_map]
    congr 1
    apply List.map_congr_left
    intro r hr
    have lt:=List.mem_range.mp hr
    simp [Function.comp_def,Nat.mul_comm n M,Nat.mul_add_div hm,Nat.div_eq_of_lt lt,Nat.mod_eq_of_lt lt]

theorem raw_radix (M:ℕ) (hm:0<M) (back:List ℕ) :
    (List.range (M^back.length)).map (readBack M back)=products (fun _=>List.range M) back.reverse := by
  induction back with
  | nil=>simp [readBack,products]
  | cons v tail ih=>
    rw [List.reverse_cons,snoc_products,←ih,List.flatMap_map,List.length_cons,pow_succ]
    exact range_blocks (fun q r=>readBack M tail q++[(v,r)]) _ M hm

theorem filter_products (menu:ℕ→List ℕ) (valid:ℕ→ℕ→Bool) (vs:List ℕ) :
    (products menu vs).filter (admissible valid)=products (fun v=>(menu v).filter (valid v)) vs := by
  induction vs with
  | nil=>simp [products,admissible]
  | cons v vs ih=>
    simp only [products,List.filter_flatMap]
    generalize menu v=xs
    induction xs with
    | nil=>simp
    | cons x xs jh=>
      rw [List.flatMap_cons,List.filter_cons]
      cases hv:valid v x
      · simp only [hv, Bool.false_eq_true, if_false, jh]
        simp [List.filter_map,admissible,Function.comp_def,hv]
      · simp only [hv, if_true,List.flatMap_cons,jh]
        congr 1
        rw [List.filter_map,←ih]
        simp [admissible,Function.comp_def,hv]
        rfl

/-- Repeated quotient/remainder from the last boundary vertex realizes the
ordered Cartesian product after the invalid coordinates are discarded. -/
theorem filtered_radix (d:Instance) (vs:List ℕ) (M:ℕ) (hm:0<M) (valid:ℕ→ℕ→Bool)
    (name:ℕ→ℕ) (menus:∀v,d.menu v=((List.range M).filter (valid v)).map name) :
    (((List.range (M^vs.length)).map (readBack M vs.reverse)).filter (admissible valid)).map
      (fun a=>a.map fun q=>(q.1,name q.2))=TightLanguage.assignments d vs :=by
  have r:=raw_radix M hm vs.reverse
  simp only [List.length_reverse,List.reverse_reverse] at r
  rw [r,filter_products]
  clear r
  induction vs with
  | nil=>simp [products,TightLanguage.assignments]
  | cons v vs ih=>
    simp [products,TightLanguage.assignments,menus,←ih,List.map_flatMap,List.flatMap_map,List.map_map,Function.comp_def]

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration


namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open WindowCSP
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- Count all size, cut, seed, boundary-radix, pivot and pivot-label trials.
This bound includes boundary tuples eventually rejected by a menu test. -/
theorem all_trials (n H t:ℕ) (hn:2≤n) (hH:1≤H) :
    let M:=H*n^(2*H)
    n*((n+1)^t*(n*(M^t*(n*M))))≤n^(6*(H*(t+1))) :=by
  let M:=H*n^(2*H)
  have nn:1≤n:=by omega
  have PH:H≤n^H:=(Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))).trans (Nat.pow_le_pow_left hn _)
  have m:M≤n^(3*H):=calc
    M ≤ n^H*n^(2*H) := Nat.mul_le_mul_right _ PH
    _ = _ := by rw [←pow_add];congr 1;omega
  have plus:n+1≤n^2:=by nlinarith [Nat.mul_le_mul_right n hn]
  have c:(n+1)^t≤n^(2*t):=by simpa [pow_mul] using Nat.pow_le_pow_left plus t
  have ht:t+1≤H*(t+1):=Nat.le_mul_of_pos_left _ hH
  change n*((n+1)^t*(n*(M^t*(n*M))))≤_
  calc
    _ = n^3*(n+1)^t*M^(t+1) := by rw [pow_succ M];ring
    _ ≤ n^3*n^(2*t)*(n^(3*H))^(t+1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ c) (Nat.pow_le_pow_left m _)
    _ = n^(3+2*t+3*H*(t+1)) := by rw [←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right nn (by nlinarith)

theorem mission_trials (n:ℕ) (e:ℚ) (hn:2≤n) (he:0<e) (hl:e<1) :
    let H:=budget (e:ℝ)+1
    let t:=min (widthBound (e:ℝ)) n
    let M:=H*n^(2*H)
    n*((n+1)^t*(n*(M^t*(n*M))))≤n^(30*parameterEnvelope (e:ℝ)):=by
  let H:=budget (e:ℝ)+1
  let t:=min (widthBound (e:ℝ)) n
  have er:0<(e:ℝ):=by exact_mod_cast he
  have el:(e:ℝ)<1:=by exact_mod_cast hl
  have ow:1≤ownerBound (e:ℝ):=by
    unfold ownerBound
    apply Nat.le_floor
    push_cast
    exact (le_div_iff₀ er).2 (by linarith)
  have h:H≤5*ownerBound (e:ℝ):=by dsimp [H,budget];omega
  have w:t+1≤widthBound (e:ℝ)+1:=Nat.succ_le_succ (Nat.min_le_left ..)
  have hwt:=Nat.mul_le_mul h w
  apply (all_trials n H t hn (by dsimp [H];omega)).trans
  apply Nat.pow_le_pow_right (by omega)
  unfold parameterEnvelope
  nlinarith

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration


open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Enumeration
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution :
    (∀(vs:List ℕ) (w:ℕ),preorder vs w=TightLanguage.cuts vs w) ∧
    (∀(d:Instance) (vs:List ℕ) (M:ℕ),0<M → ∀(valid:ℕ→ℕ→Bool) (name:ℕ→ℕ),
      (∀v,d.menu v=((List.range M).filter (valid v)).map name) →
      (((List.range (M^vs.length)).map (readBack M vs.reverse)).filter (admissible valid)).map
        (fun a=>a.map fun q=>(q.1,name q.2))=TightLanguage.assignments d vs) ∧
    ∀(n:ℕ) (e:ℚ),2≤n → 0<e → e<1 →
      let H:=budget (e:ℝ)+1
      let t:=min (widthBound (e:ℝ)) n
      let M:=H*n^(2*H)
      n*((n+1)^t*(n*(M^t*(n*M))))≤n^(30*parameterEnvelope (e:ℝ)) := ⟨preorder_exact,filtered_radix,mission_trials⟩
