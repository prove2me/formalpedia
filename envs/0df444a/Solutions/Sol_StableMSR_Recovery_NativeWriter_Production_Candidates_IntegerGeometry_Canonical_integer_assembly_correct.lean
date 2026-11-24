-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.integer_assembly_correct
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-24T01:20:27.938586+00:00
-- url     : https://prove2.me/submissions/84720514-352b-453f-b510-19aae62e210c

import Definitions.Def_StableMSR_ExecutableIntegerAssembly
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_computed_integer_instance
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_assembly_recognizes_original
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical
open Compiler OracleQueries SingleCircuit SingleRAM WindowCSP
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000

theorem positive_iff (x:World) (a b:ℤ) (hm:IsMetricArray x.dist) :
    positive x.n a b=true ↔ 0<MinSumFPT.oracleAnswer x.dist a b:=by
  obtain ⟨metric,eq⟩:=hm
  letI:=metric
  unfold positive MinSumFPT.oracleAnswer
  cases ha:MinSumFPT.toPoint x.n a <;> cases hb:MinSumFPT.toPoint x.n b <;> simp [←eq,dist_pos]
theorem piece_key (x:World) (u i:ℕ) :
    (Bits.piece x.n x.mem u i).Nonempty ↔ i∈WindowProfiles.keys x u:=by
  change (WindowProfiles.piece x u i).Nonempty ↔ _
  simp only [Finset.Nonempty,WindowProfiles.piece,WindowProfiles.keys,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]

theorem integer_step (correct:∀(x:World) (r h:ℕ) (m:ℤ→ℤ),
    0<x.n → 0<scale x (r/x.n) → IsMetricArray x.dist → Prepared x (scale x (r/x.n)) m →
    integerData x.n x.mem m r h=arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h))
    (x:World) (h w r:ℕ) (T:ℕ→ℤ→ℤ) (a:Assembly)
    (hn:0<x.n) (hm:IsMetricArray x.dist) (prep:0<scale x (r/x.n) → Prepared x (scale x (r/x.n)) (T (r/x.n))) :
    appendInteger x.n h w x.mem T a r=Canonical.appendRegion x h w r a:=by
  have pos:=positive_iff x (x.mem (sceneBase x (r/x.n))) (x.mem (sceneBase x (r/x.n)+1)) hm
  change (positive x.n _ _=true ↔ 0<scale x (r/x.n)) at pos
  by_cases key:r%x.n∈WindowProfiles.keys x (r/x.n)
  · have yes:=(piece_key x (r/x.n) (r%x.n)).mpr key
    by_cases hp:0<scale x (r/x.n)
    · have live:=pos.mpr hp
      simp only [sceneBase] at live
      simpa only [appendInteger,Canonical.appendRegion,Canonical.region,if_pos yes,if_pos key,if_pos hp,if_pos live,correct x r h (T _) hn hp hm (prep hp)]
    · have stop:¬positive x.n (x.mem (sceneBase x (r/x.n))) (x.mem (sceneBase x (r/x.n)+1))=true:=fun h=>hp (pos.mp h)
      simp only [sceneBase] at stop
      simp only [appendInteger,Canonical.appendRegion,if_pos yes,if_pos key,if_neg hp,if_neg stop]
  · have missing:¬(Bits.piece x.n x.mem (r/x.n) (r%x.n)).Nonempty:=fun h=>key ((piece_key ..).mp h)
    simp only [appendInteger,Canonical.appendRegion,if_neg missing,if_neg key]

theorem same_fold {A B:Type} (xs:List A) (f g:B→A→B) (z:B) (same:∀v∈xs,∀a,f a v=g a v) : xs.foldl f z=xs.foldl g z:=by
  induction xs generalizing z with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.foldl_cons];rw [same x List.mem_cons_self z]
    exact ih _ (fun y hy=>same y (List.mem_cons_of_mem _ hy))

theorem build_eq (correct:∀(x:World) (r h:ℕ) (m:ℤ→ℤ),
    0<x.n → 0<scale x (r/x.n) → IsMetricArray x.dist → Prepared x (scale x (r/x.n)) m →
    integerData x.n x.mem m r h=arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h))
    (x:World) (h w:ℕ) (T:ℕ→ℤ→ℤ) (hn:0<x.n) (hm:IsMetricArray x.dist)
    (prep:∀u<x.rows,0<scale x u → Prepared x (scale x u) (T u)) :
    buildInteger x.n x.rows h w x.mem T=Canonical.assembly x h w:=by
  let R:=x.rows*x.n
  let f:=appendInteger x.n h w x.mem T
  let g:=fun (a:Assembly) r=>Canonical.appendRegion x h w r a
  have eq:(List.range R).foldl f emptyAssembly=(List.range R).foldl g emptyAssembly:=by
    apply same_fold
    intro r hr a
    have hu:r/x.n<x.rows:=(Nat.div_lt_iff_lt_mul hn).mpr (List.mem_range.mp hr)
    exact integer_step correct x h w r T a hn hm (prep _ hu)
  exact congrArg (fun a=>padAssembly a R) eq
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical

open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
theorem solution (x:World) (e:ℚ) (T:ℕ→ℤ→ℤ) (hn:0<x.n) (hm:IsMetricArray x.dist)
  (prep:∀u<x.rows,0<scale x u → Prepared x (scale x u) (T u)) :
  let a:=Canonical.buildInteger x.n x.rows (budget (e:ℝ)) (widthBound (e:ℝ)) x.mem T
  a=Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ)) ∧ RegionalLanguage x e a.gates a.roots := by
  have eq:=Canonical.build_eq Canonical.computed_integer_instance x (budget (e:ℝ)) (widthBound (e:ℝ)) T hn hm prep
  rw [eq]
  exact ⟨rfl,Canonical.assembly_recognizes_original x e hn⟩
