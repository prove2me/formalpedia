-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Relative.native_single_region_packet
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T23:18:07.531774+00:00
-- url     : https://prove2.me/submissions/9bd187c6-f9a8-4df9-9d6a-379417372336
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_ordered_production_table
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_chart_packet_decoder
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_regional_production_size
set_option linter.all false
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace StableMSR.Recovery.NativeWriter.Production
open Compiler OracleQueries SingleCircuit WindowCSP Relative
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

theorem source_frame {n : ℕ} {s t : Store} (h:∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a))
    {a j : ℕ} {op:Gate} (o:Record n s a j op) : Record n t a j op :=
  ⟨(h 1 (by decide) (by decide) a).trans o.1,(h 2 (by decide) (by decide) a).trans o.2.1,
    (h 3 (by decide) (by decide) a).trans o.2.2.1,fun k hk=>(h 5 (by decide) (by decide) _).trans (o.2.2.2 k hk)⟩

theorem from_production_source
    (src:∃ c D b : ℕ,∀e : ℚ,0<e → e<1 → ∃cmd : Cmd, Source e c D b cmd)
    (decoderLaw:∃ (A : ℕ) (cmd : Cmd),∀(x : World) (s : Store) (r p : ℕ) (a : Script),
    Ready x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → Stored x.n s.imem a →
    ∃t z, Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+a.events.length) ∧
      Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(a.packet.gates.size:ℤ) ∧
      (∀j<a.packet.gates.size, Record x.n t (p+j) j (gateAt a.packet.gates j)) ∧
      DirAt t r (a.packet.token,a.packet.gates.size) ∧
      (∀q<p,∀j op,Record x.n s q j op → Record x.n t q j op) ∧
      ∀q<r,∀v,DirAt s q v → DirAt t q v)
    (regional:∀(x:World) (e:ℚ) (r:ℕ),0<e → e<1 → 2≤x.n →
      let h:=budget (e:ℝ);let w:=widthBound (e:ℝ);let a:=regionalScript x h w r
      a.packet=Relative.packet x h w r ∧ a.events.length≤x.n^(75*parameterEnvelope (e:ℝ))) :
    ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t := by


  obtain ⟨c,D,b,source⟩:=src
  obtain ⟨A,decode,dr⟩:=decoderLaw
  refine ⟨c+2*A,D+1,b+75,?_⟩
  intro e he hl
  obtain ⟨enumerate,en⟩:=source e he hl
  refine ⟨.seq enumerate decode,?_⟩
  intro x s k kn metric rd r p slot off actual
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let a:=regionalScript x h w r
  obtain ⟨t,z,first,cost,ready,regs,mem,table⟩:=en x s k kn metric rd r p slot off actual
  obtain ⟨v,y,second,bound,endReady,low,last,gates,dir,older,dirs⟩:=dr x t r p a ready
    ((regs 3 (by simp)).trans slot) ((regs 4 (by simp)).trans off) table
  obtain ⟨eq,sz⟩:=regional x e r he hl (by omega)
  change a.packet=Relative.packet x h w r at eq
  change a.events.length≤_ at sz
  rw [eq] at last gates dir
  refine ⟨v,z+y,.seq first second,?_,⟨endReady,fun i hi=>(low i hi).trans (regs i hi),last,gates,?_,?_,?_⟩⟩
  · let E:=parameterEnvelope (e:ℝ)
    have hc:1≤x.cap:=by unfold World.cap;omega
    have nc:1+x.n≤x.cap:=by unfold World.cap;omega
    have hn:1≤x.n:=by omega
    have pow1:1≤x.n^(75*E):=Nat.one_le_pow _ _ hn
    have size:1+a.events.length≤2*x.n^(75*E):=by change a.events.length≤x.n^(75*E) at sz;omega
    have d1:x.cap^D≤x.cap^(D+1):=Nat.pow_le_pow_right hc (by omega)
    have d2:x.cap≤x.cap^(D+1):=by simpa using (Nat.pow_le_pow_right (n:=x.cap) hc (show 1≤D+1 by omega))
    have e1:x.n^(b*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
    have e2:x.n^(75*E)≤x.n^((b+75)*E):=Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E (by omega))
    have left:=cost.trans (Nat.mul_le_mul (Nat.mul_le_mul_left c d1) e1)
    have right:y≤(2*A)*x.cap^(D+1)*x.n^((b+75)*E):=calc
      y ≤ A*(1+x.n)*(1+a.events.length) := bound
      _ ≤ A*x.cap^(D+1)*(2*x.n^(75*E)) := Nat.mul_le_mul (Nat.mul_le_mul_left A (nc.trans d2)) size
      _ = (2*A)*x.cap^(D+1)*x.n^(75*E) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ e2
    simpa only [Nat.add_mul] using Nat.add_le_add left right
  · intro b hb;change some ((Relative.packet x h w r).token,(Relative.packet x h w r).gates.size)=some b at hb
    cases hb;exact dir
  · intro q hq j op o;exact older q hq j op (source_frame mem o)
  · intro q hq b o;exact dirs q hq b ⟨(mem 4 (by decide) (by decide) q).trans o.1,(mem 6 (by decide) (by decide) q).trans o.2⟩

end StableMSR.Recovery.NativeWriter.Production
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit
theorem solution :
    ∃ c D b : ℕ, ∀e : ℚ, 0<e → e<1 → ∃cmd:Cmd,
      ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
      ∀r p : ℕ, s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
      ∃t z, Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
        PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p .region s t := from_production_source native_ordered_production_table native_chart_packet_decoder regional_production_size
