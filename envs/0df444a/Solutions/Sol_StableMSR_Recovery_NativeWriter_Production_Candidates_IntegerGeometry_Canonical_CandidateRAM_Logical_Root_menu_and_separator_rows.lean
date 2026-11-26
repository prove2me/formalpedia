-- Prove2me | solution 1 for StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root.menu_and_separator_rows
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-25T05:03:30.548045+00:00
-- url     : https://prove2.me/submissions/b0f00497-5582-4b73-ba73-1354fcc5d8f3

import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_build_regional_menus
import Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Root_write_regional_separators
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem solution :
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:Logical.State,Logical.Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∀v:Logical.State, Scene.GeometryImage s.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) (budget (e:ℝ)) u v →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Logical.Executes x.n s.imem Scene.menuAndRows v t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape CandidateRAM.Naming.name d (widthBound (e:ℝ)) ∧
      (let o:=Logical.offsets d.n (Logical.sizes d.n (budget (e:ℝ)))
       (∀j<d.n,t.heap (Logical.cursorAt o 0+j)=v.heap (Logical.cursorAt o 0+j)) ∧
       (∀j<d.n,∀z<d.n,t.heap (Logical.cursorAt o 4+(j*d.n+z))=v.heap (Logical.cursorAt o 4+(j*d.n+z)))) := by
  obtain ⟨c₁,D₁,b₁,build⟩ := Root.build_regional_menus
  obtain ⟨c₂,D₂,b₂,cuts⟩ := Root.write_regional_separators
  refine ⟨1+c₁+c₂,D₁+D₂,b₁+b₂,?_⟩
  intro e ep e1 x s hk hkn ready bounded r p row ptr valid key u prepared v geo
  obtain ⟨z,i,make,mi,menus⟩ := build e ep e1 x s hk hkn ready bounded r p row ptr valid key u prepared v geo
  obtain ⟨t,j,write,mj,out,frame⟩ := cuts e ep e1 x s hk hkn ready bounded r p row ptr valid key u prepared v geo z menus
  have hn : 0<x.n := by omega
  let E := parameterEnvelope (e:ℝ)
  let X := x.cap^(D₁+D₂)*x.n^((b₁+b₂)*E)
  have hc : 1 ≤ x.cap := by unfold World.cap; omega
  have big (d b : ℕ) (hd : d ≤ D₁+D₂) (hb : b ≤ b₁+b₂) :
      x.cap^d*x.n^(b*E) ≤ X :=
    Nat.mul_le_mul (Nat.pow_le_pow_right hc hd)
      (Nat.pow_le_pow_right hn (Nat.mul_le_mul_right E hb))
  have xi : i ≤ c₁*X := by
    calc i ≤ c₁*x.cap^D₁*x.n^(b₁*E) := mi
         _ = c₁*(x.cap^D₁*x.n^(b₁*E)) := Nat.mul_assoc _ _ _
         _ ≤ c₁*X := Nat.mul_le_mul_left _ (big _ _ (by omega) (by omega))
  have xj : j ≤ c₂*X := by
    calc j ≤ c₂*x.cap^D₂*x.n^(b₂*E) := mj
         _ = c₂*(x.cap^D₂*x.n^(b₂*E)) := Nat.mul_assoc _ _ _
         _ ≤ c₂*X := Nat.mul_le_mul_left _ (big _ _ (by omega) (by omega))
  have nonzero : 1 ≤ X := Nat.mul_pos (Nat.one_le_pow _ _ hc) (Nat.one_le_pow _ _ hn)
  refine ⟨t,_,Executes.seq make write,?_,out,?_⟩
  · calc 1+i+j ≤ X + c₁*X + c₂*X := Nat.add_le_add (Nat.add_le_add nonzero xi) xj
         _ = (1+c₁+c₂)*x.cap^(D₁+D₂)*x.n^((b₁+b₂)*E) := by dsimp [X]; ring
  · let o := offsets x.n (sizes x.n (budget (e:ℝ)))
    have preserve (i : ℕ) (hi : i < cursorAt o 5) := (frame i hi).trans (menus.geometry i hi)
    constructor
    · intro j hj
      change t.heap (cursorAt o 0+j)=v.heap (cursorAt o 0+j)
      apply preserve
      change j < x.n at hj
      simp [o,offsets,cursorAt] <;> omega
    · intro a ha z hz
      change t.heap (cursorAt o 4+(a*x.n+z))=v.heap (cursorAt o 4+(a*x.n+z))
      apply preserve
      change a < x.n at ha
      change z < x.n at hz
      have flat : a*x.n+z < x.n*x.n := calc
        a*x.n+z < a*x.n+x.n := Nat.add_lt_add_left hz _
        _ = (a+1)*x.n := by ring
        _ ≤ x.n*x.n := Nat.mul_le_mul_right x.n ha
      simp [o,offsets,cursorAt] <;> omega
