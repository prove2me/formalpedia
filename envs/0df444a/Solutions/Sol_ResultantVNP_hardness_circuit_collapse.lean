-- Prove2me | solution 1 for ResultantVNP.hardness_circuit_collapse
-- status  : ACCEPTED   (prove)
-- author  : @gjindal
-- created : 2026-11-14T10:57:03.421626+00:00
-- url     : https://prove2.me/submissions/ccea2d13-90a7-4db8-ba7d-b704d3d2b7e7

import Mathlib
import Definitions.Def_ResultantVNP_IsVNPHardPProj
import Definitions.Def_ResultantVNP_HasPolySizeCircuits

set_option autoImplicit false

namespace HardnessProjection

open ResultantVNP

private def projectNode {σ τ : Type} (ρ : σ → τ ⊕ ℂ) : Node σ → Node τ
  | .var x => Sum.elim Node.var Node.const (ρ x)
  | .const a => .const a
  | .add i j => .add i j
  | .mul i j => .mul i j

private lemma project_reads {σ τ : Type} (ρ : σ → τ ⊕ ℂ) (nd : Node σ) (k : ℕ) :
    (projectNode ρ nd).ReadsBelow k = nd.ReadsBelow k := by
  cases nd with
  | var x => cases h : ρ x <;> simp [projectNode, Node.ReadsBelow, h]
  | const a => rfl
  | add i j => rfl
  | mul i j => rfl

def projectCircuit {σ τ : Type} (ρ : σ → τ ⊕ ℂ) (C : Circuit σ) : Circuit τ where
  nodes := C.nodes.map (projectNode ρ)
  nonempty := by
    intro h
    exact C.nonempty (List.eq_nil_of_map_eq_nil h)
  wf := by
    intro k hk
    have h := C.wf k (by simpa only [List.length_map] using hk)
    simpa only [List.getElem_map, project_reads] using h

private noncomputable def subst {σ τ : Type} (ρ : σ → τ ⊕ ℂ) :
    MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial τ ℂ :=
  MvPolynomial.aeval (fun x => Sum.elim MvPolynomial.X MvPolynomial.C (ρ x))

private lemma project_eval {σ τ : Type} (ρ : σ → τ ⊕ ℂ)
    (vs : List (MvPolynomial σ ℂ)) (nd : Node σ) :
    (projectNode ρ nd).eval (vs.map (subst ρ)) = subst ρ (nd.eval vs) := by
  have hg (i : ℕ) : (vs.map (subst ρ)).getD i 0 = subst ρ (vs.getD i 0) := by
    simpa only [map_zero] using
      List.getD_map (l := vs) (d := (0 : MvPolynomial σ ℂ)) (n := i) (subst ρ)
  cases nd with
  | var x => cases h : ρ x <;> simp [projectNode, Node.eval, subst, h]
  | const a => simp [projectNode, Node.eval, subst]
  | add i j => simp only [projectNode, Node.eval, hg, map_add]
  | mul i j => simp only [projectNode, Node.eval, hg, map_mul]

private lemma project_fold {σ τ : Type} (ρ : σ → τ ⊕ ℂ)
    (ns : List (Node σ)) (vs : List (MvPolynomial σ ℂ)) :
    (ns.map (projectNode ρ)).foldl (fun vals nd => vals ++ [nd.eval vals])
        (vs.map (subst ρ)) =
      (ns.foldl (fun vals nd => vals ++ [nd.eval vals]) vs).map (subst ρ) := by
  induction ns generalizing vs with
  | nil => rfl
  | cons nd ns ih =>
    simp only [List.map_cons, List.foldl_cons]
    simpa only [List.map_append, List.map_cons, List.map_nil, project_eval] using
      ih (vs ++ [nd.eval vs])

theorem projectCircuit_value {σ τ : Type} (ρ : σ → τ ⊕ ℂ) (C : Circuit σ) :
    (projectCircuit ρ C).value =
      MvPolynomial.aeval (fun x => Sum.elim MvPolynomial.X MvPolynomial.C (ρ x)) C.value := by
  have hv : (projectCircuit ρ C).values = C.values.map (subst ρ) := by
    simpa only [Circuit.values, projectCircuit, List.map_nil] using project_fold ρ C.nodes []
  unfold Circuit.value
  rw [hv]
  simpa only [map_zero, subst] using
    List.getLastD_map (f := subst ρ) (l := C.values) (a := (0 : MvPolynomial σ ℂ))

theorem projectCircuit_size {σ τ : Type} (ρ : σ → τ ⊕ ℂ) (C : Circuit σ) :
    (projectCircuit ρ C).size = C.size := by
  have hg : ∀ nd : Node σ, (projectNode ρ nd).isGate = nd.isGate := by
    intro nd
    cases nd with
    | var x => cases h : ρ x <;> simp [projectNode, Node.isGate, h]
    | const a => rfl
    | add i j => rfl
    | mul i j => rfl
  simp [Circuit.size, projectCircuit, List.countP_map, Function.comp_def, hg]

end HardnessProjection

namespace HardnessCollapse
open ResultantVNP MvPolynomial

private def PB (f : ℕ → ℕ) : Prop := ∃ a b : ℕ, ∀ n, f n ≤ a * (n+1)^b

private lemma pb_of_poly {f : ℕ → ℕ} (h : PolyBounded f) : PB f := by
  obtain ⟨c,hc⟩ := h
  refine ⟨2*c,c,fun n => (hc n).trans ?_⟩
  have hp : n^c ≤ (n+1)^c := Nat.pow_le_pow_left (by omega) c
  have hp1 : 1 ≤ (n+1)^c := Nat.one_le_pow c (n+1) (by omega)
  nlinarith

private lemma poly_of_pb {f : ℕ → ℕ} (h : PB f) : PolyBounded f := by
  obtain ⟨a,b,h⟩ := h
  let c := a * 2^b+b
  refine ⟨c,fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    have hh := h 0
    simp only [zero_add, one_pow, mul_one] at hh
    have hp : 1 ≤ 2^b := Nat.one_le_pow b 2 (by omega)
    have ha := Nat.mul_le_mul_left a hp
    simp only [mul_one] at ha
    dsimp [c]
    omega
  · have hn1 : 1 ≤ n := by omega
    have hp : (n+1)^b ≤ (2*n)^b := Nat.pow_le_pow_left (by omega) b
    rw [mul_pow] at hp
    have hbc : b ≤ c := by dsimp [c]; omega
    have hp' : n^b ≤ n^c := Nat.pow_le_pow_right hn1 hbc
    have ha : a*2^b ≤ c := by dsimp [c]; omega
    calc
      f n ≤ a*(n+1)^b := h n
      _ ≤ a*(2^b*n^b) := Nat.mul_le_mul_left a hp
      _ = (a*2^b)*n^b := by ring
      _ ≤ c*n^c := Nat.mul_le_mul ha hp'
      _ ≤ c*n^c+c := by omega

private lemma pb_const (c : ℕ) : PB (fun _ => c) := ⟨c,0,by simp⟩
private lemma pb_id : PB (fun n => n) := ⟨1,1,by simp⟩

private lemma pb_add {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n + g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a+c,b+d,fun n => ?_⟩
  have hb : (n+1)^b ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  have hd : (n+1)^d ≤ (n+1)^(b+d) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    f n + g n ≤ a*(n+1)^b + c*(n+1)^d := Nat.add_le_add (hf n) (hg n)
    _ ≤ a*(n+1)^(b+d) + c*(n+1)^(b+d) :=
      Nat.add_le_add (Nat.mul_le_mul_left a hb) (Nat.mul_le_mul_left c hd)
    _ = (a+c)*(n+1)^(b+d) := by ring

private lemma pb_mul {f g : ℕ → ℕ} (hf : PB f) (hg : PB g) :
    PB (fun n => f n * g n) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a*c,b+d,fun n => ?_⟩
  calc
    f n*g n ≤ (a*(n+1)^b)*(c*(n+1)^d) := Nat.mul_le_mul (hf n) (hg n)
    _ = (a*c)*(n+1)^(b+d) := by rw [pow_add]; ring

private lemma pb_pow {f : ℕ → ℕ} (hf : PB f) (k : ℕ) : PB (fun n => f n^k) := by
  obtain ⟨a,b,hf⟩ := hf
  refine ⟨a^k,b*k,fun n => ?_⟩
  calc
    f n^k ≤ (a*(n+1)^b)^k := Nat.pow_le_pow_left (hf n) k
    _ = a^k*(n+1)^(b*k) := by rw [mul_pow,pow_mul]

private lemma pb_mono {f g : ℕ → ℕ} (hg : PB g) (h : ∀ n, f n ≤ g n) : PB f := by
  obtain ⟨a,b,hg⟩ := hg
  exact ⟨a,b,fun n => (h n).trans (hg n)⟩

private lemma poly_mono {f g : ℕ → ℕ} (hg : PolyBounded g) (h : ∀ n, f n ≤ g n) :
    PolyBounded f := poly_of_pb (pb_mono (pb_of_poly hg) h)

private lemma degree_aeval {σ τ : Type} (f : σ → MvPolynomial τ ℂ)
    (hf : ∀ x, (f x).totalDegree ≤ 1) (p : MvPolynomial σ ℂ) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  classical
  have he : aeval f p = ∑ v ∈ p.support, aeval f (monomial v (p.coeff v)) := by
    conv_lhs => rw [p.as_sum,map_sum]
  rw [he]
  apply totalDegree_finsetSum_le
  intro v hv
  rw [aeval_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [algebraMap_eq,totalDegree_C,zero_add]
  apply le_trans (totalDegree_finsetProd _ _) (le_trans ?_ (le_totalDegree hv))
  change (∑ x ∈ v.support, (f x ^ v x).totalDegree) ≤ ∑ x ∈ v.support, v x
  apply Finset.sum_le_sum
  intro x hx
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (v x) (hf x))

private lemma vnp_bounds (f : PolyFamily) (hf : f ∈ VNP) :
    PolyBounded f.nvars ∧ PolyBounded (fun n => (f.p n).totalDegree) := by
  obtain ⟨g, hg, q, hq, hsum⟩ := hf
  refine ⟨poly_mono hg.1 (fun n => ?_), poly_mono hg.2.1 (fun n => ?_)⟩
  · obtain ⟨h,_⟩ := hsum n
    omega
  · obtain ⟨h,heq⟩ := hsum n
    rw [heq]
    apply totalDegree_finsetSum_le
    intro y hy
    apply degree_aeval
    intro v
    generalize Fin.cast h v = w
    refine Fin.addCases ?_ ?_ w
    · intro i; simp only [Fin.append_left, totalDegree_X, le_refl]
    · intro j; rw [Fin.append_right, totalDegree_C]; omega

private lemma vp_subset_vnp : VP ⊆ VNP := by
  intro f hf
  refine ⟨f, hf, fun _ => 0, ⟨0, by simp⟩, ?_⟩
  intro n
  refine ⟨(Nat.add_zero _).symm, ?_⟩
  have hρ (y : Fin 0 → Fin 2) :
      (fun v : Fin (f.nvars n) =>
        Fin.append (fun i : Fin (f.nvars n) =>
          (MvPolynomial.X i : MvPolynomial (Fin (f.nvars n)) ℂ))
          (fun j : Fin 0 => MvPolynomial.C (((y j : ℕ) : ℂ)))
          (Fin.cast (Nat.add_zero _).symm v)) = MvPolynomial.X := by
    funext v
    simp [Fin.append, Fin.addCases, Fin.cast]
    apply Fin.ext
    rfl
  simp only [hρ]
  simp

theorem collapse {τ : ℕ → Type} (G : ∀ m, MvPolynomial (τ m) ℂ) (lo : ℕ)
    (hlo : 1 ≤ lo) (hhard : IsVNPHardPProj G lo) (hcirc : HasPolySizeCircuits G) :
    VP = VNP := by
  apply Set.Subset.antisymm vp_subset_vnp
  intro f hf
  obtain ⟨hnvars,hdegree⟩ := vnp_bounds f hf
  obtain ⟨t,ht,htproj⟩ := hhard f hf
  obtain ⟨c,hc⟩ := hcirc
  have hsize : PolyBounded (fun n => c*(t n)^c+c) :=
    poly_of_pb (pb_add (pb_mul (pb_const c) (pb_pow (pb_of_poly ht) c)) (pb_const c))
  obtain ⟨b,hb⟩ := hsize
  refine ⟨hnvars,hdegree,b,fun n => ?_⟩
  obtain ⟨hlt,ρ,hρ⟩ := htproj n
  obtain ⟨C,hval,hCs⟩ := hc (t n) (hlo.trans hlt)
  refine ⟨HardnessProjection.projectCircuit ρ C, ?_, ?_⟩
  · rw [HardnessProjection.projectCircuit_value,hval]
    exact hρ
  · rw [HardnessProjection.projectCircuit_size]
    exact hCs.trans (hb n)

end HardnessCollapse

theorem solution {τ : ℕ → Type} (G : ∀ m, MvPolynomial (τ m) ℂ) (lo : ℕ)
    (hlo : 1 ≤ lo) (hhard : ResultantVNP.IsVNPHardPProj G lo)
    (hcirc : ResultantVNP.HasPolySizeCircuits G) : ResultantVNP.VP = ResultantVNP.VNP :=
  HardnessCollapse.collapse G lo hlo hhard hcirc

#print axioms solution
