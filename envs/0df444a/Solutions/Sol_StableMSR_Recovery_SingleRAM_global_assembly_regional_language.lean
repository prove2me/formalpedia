-- Prove2me | solution 1 for StableMSR.Recovery.SingleRAM.global_assembly_regional_language
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-23T18:11:48.092688+00:00
-- url     : https://prove2.me/submissions/64b7af6b-6042-450b-92ac-19d7d54a0057

import Definitions.Def_StableMSR_DenseGlobalAssembly
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 15000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.SingleRAM
namespace StableMSR.Recovery.GlobalAssemblyProof
open SingleCircuit SingleRAM
def placed (g G:Gates) (t:ℕ) := t+g.size≤G.size ∧
  ∀p<g.size,gateAt G (t+p)=relocateGate t (gateAt g p)
def append (a b:Gates) := a ++ b.map (relocateGate a.size)
noncomputable def step {n : ℕ} (L : ℕ→List (Cluster n)→Prop) (p : ℕ)
    (s : List (Cluster n)) : Gate→Prop
  | .stop=>False
  | .atom m=>s=WindowMasks.emit (Finset.univ.filter (fun i : Point n=>m.contains i.val))
  | .both a b => a<p ∧ b<p ∧ ∃u v,L a u ∧ L b v ∧ s=u++v
  | .either a b => (a<p ∧ L a s) ∨ (b<p ∧ L b s)
lemma unfoldLang {n : ℕ} (g : Gates) (p : ℕ) (s : List (Cluster n)) :
    Language n g p s ↔ p<g.size ∧ step (Language n g) p s (gateAt g p) := by
  constructor
  · intro h
    cases h with
    | lit sz eq=>exact ⟨sz,by rw [eq];rfl⟩
    | both sz eq ha hb hl hr=>exact ⟨sz,by rw [eq]; exact ⟨ha,hb,_,_,hl,hr,rfl⟩⟩
    | left sz eq ha hl=>exact ⟨sz,by rw [eq];exact Or.inl ⟨ha,hl⟩⟩
    | right sz eq hb hr=>exact ⟨sz,by rw [eq];exact Or.inr ⟨hb,hr⟩⟩
  · rintro ⟨sz,h⟩
    cases eq : gateAt g p with
    | stop=>rw [eq] at h;exact False.elim h
    | atom m=>rw [eq] at h; change s=_ at h; subst s; exact .lit sz eq
    | both a b=>
      rw [eq] at h
      obtain ⟨ha,hb,u,v,hu,hv,rfl⟩:=h
      exact .both sz eq ha hb hu hv
    | either a b=>
      rw [eq] at h
      rcases h with ⟨ha,h⟩|⟨hb,h⟩
      · exact .left sz eq ha h
      · exact .right sz eq hb h
theorem placement_preserves_words {n : ℕ} (g G : Gates) (t : ℕ) (good : placed g G t)
    (p : ℕ) (hp : p<g.size) (s : List (Cluster n)) :
    Language n G (t+p) s ↔ Language n g p s := by
  induction p using Nat.strong_induction_on generalizing s with
  | h p ih=>
    have sz:=good.1
    rw [unfoldLang G,unfoldLang g,good.2 p hp]
    simp only [hp,show t+p<G.size by omega,true_and]
    cases eq : gateAt g p with
    | stop=>rfl
    | atom m=>rfl
    | both a b=>
      simp only [relocateGate,step,Nat.add_lt_add_iff_left]
      constructor
      · rintro ⟨ha,hb,u,v,hu,hv,hs⟩
        exact ⟨ha,hb,u,v,(ih a ha (by omega) u).1 hu,(ih b hb (by omega) v).1 hv,hs⟩
      · rintro ⟨ha,hb,u,v,hu,hv,hs⟩
        exact ⟨ha,hb,u,v,(ih a ha (by omega) u).2 hu,(ih b hb (by omega) v).2 hv,hs⟩
    | either a b=>
      simp only [relocateGate,step,Nat.add_lt_add_iff_left]
      constructor
      · rintro (⟨ha,hu⟩|⟨hb,hv⟩)
        · exact Or.inl ⟨ha,(ih a ha (by omega) s).1 hu⟩
        · exact Or.inr ⟨hb,(ih b hb (by omega) s).1 hv⟩
      · rintro (⟨ha,hu⟩|⟨hb,hv⟩)
        · exact Or.inl ⟨ha,(ih a ha (by omega) s).2 hu⟩
        · exact Or.inr ⟨hb,(ih b hb (by omega) s).2 hv⟩
lemma relocateZero (op : Gate) : relocateGate 0 op=op := by cases op <;> simp [relocateGate]
theorem append_placements (a b : Gates) : placed a (append a b) 0 ∧ placed b (append a b) a.size := by
  constructor
  · refine ⟨by simp [append],?_⟩
    intro p hp
    simp only [Nat.zero_add,relocateZero,gateAt,append,Array.getElem?_append_left hp]
  · refine ⟨by simp [append],?_⟩
    intro p hp
    have hi : a.size≤a.size+p := by omega
    simp only [gateAt,append,Array.getElem?_append_right hi,Nat.add_sub_cancel_left,Array.getElem?_map]
    simp [getElem?_pos b p hp]

end StableMSR.Recovery.GlobalAssemblyProof
namespace StableMSR.Recovery.GlobalAssemblyProof
open SingleCircuit SingleRAM SingleCodes SingleWindows WindowCSP Compiler OracleQueries
open StableMSR.Recovery.WindowProfiles (piece keys)
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 500000

def classifies (x:World) (h w u i:ℕ) (lang:List (Cluster x.n)→Prop) : Prop :=
  (i∉keys x u → ∀L,lang L ↔ L=[]) ∧
  (i∈keys x u → scale x u≤0 → ∀L,¬lang L) ∧
  (i∈keys x u → 0<scale x u →
    let gen:=generates x (piece x u i) (scale x u) h w
    (∀L,lang L → L.Nodup ∧ gen L.toFinset) ∧ ∀Q,gen Q → ∃L,lang L ∧ L.toFinset=Q)

def slot (x:World) (h w r:ℕ) (g:Gates) (p:ℕ) :=
  p<g.size ∧ classifies x h w (r/x.n) (r%x.n) (Language x.n g p)

def valid (x:World) (h w r:ℕ) (a:Assembly) :=
  2≤a.gates.size ∧ gateAt a.gates 0=.atom [] ∧ gateAt a.gates 1=.stop ∧
    ∀j<r,slot x h w j a.gates (a.roots j)

theorem prefix_placement (g extra:Gates) : placed g (g++extra) 0 := by
  refine ⟨by simp,?_⟩
  intro p hp;simp [gateAt,Array.getElem?_append_left hp,relocateZero]

theorem same_words {n:ℕ} {g G:Gates} (pref:placed g G 0) {p:ℕ} (hp:p<g.size) :
    Language n G p=Language n g p := by
  funext L;apply propext;simpa only [Nat.zero_add] using placement_preserves_words g G 0 pref p hp L

theorem transport_slot (x:World) (h w j:ℕ) {g G:Gates} (pref:placed g G 0) {p:ℕ}
    (s:slot x h w j g p) : slot x h w j G p := by
  obtain ⟨hp,lang⟩:=s
  have le:g.size≤G.size:=by simpa only [Nat.zero_add] using pref.1
  exact ⟨hp.trans_le le,(same_words pref hp).symm ▸ lang⟩

theorem initial (x:World) (h w:ℕ) : valid x h w 0 emptyAssembly := by
  refine ⟨by decide,rfl,rfl,?_⟩;intro j hj;omega

theorem advance (x:World) (h w r:ℕ) (a b:Assembly) (old:valid x h w r a)
    (pref:placed a.gates b.gates 0) (roots:∀j<r,b.roots j=a.roots j)
    (last:slot x h w r b.gates (b.roots r)) : valid x h w (r+1) b := by
  obtain ⟨sz,z,s,prior⟩:=old
  have le:a.gates.size≤b.gates.size:=by simpa only [Nat.zero_add] using pref.1
  have tag (p:ℕ) (lt:p<a.gates.size):gateAt b.gates p=gateAt a.gates p:=by
    simpa only [Nat.zero_add,relocateZero] using pref.2 p lt
  refine ⟨sz.trans le,(tag 0 (by omega)).trans z,(tag 1 (by omega)).trans s,?_⟩
  intro j hj
  by_cases eq:j=r
  · simpa only [eq] using last
  · have jr:j<r:=by omega
    rw [roots j jr];exact transport_slot x h w j pref (prior j jr)

theorem default_word (n:ℕ) (g:Gates) (inside:0<g.size) (gate:gateAt g 0=.atom []) (L:List (Cluster n)) :
    Language n g 0 L ↔ L=[] := by
  rw [unfoldLang,gate];simp [step,inside,WindowMasks.emit]

theorem default_stop (n:ℕ) (g:Gates) (gate:gateAt g 1=.stop) (L:List (Cluster n)) :
    ¬Language n g 1 L := by
  rw [unfoldLang,gate];simp [step]
end StableMSR.Recovery.GlobalAssemblyProof
namespace StableMSR.Recovery.GlobalAssemblyProof
open SingleCircuit SingleRAM SingleCodes SingleWindows WindowCSP Compiler OracleQueries
open StableMSR.Recovery.WindowProfiles (piece keys)
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem append_valid (x:World) (h w r:ℕ) (a:Assembly) (hn:0<x.n) (live:r<x.rows*x.n)
    (correct:∀u<x.rows,∀i<x.n,i∈keys x u → 0<scale x u → LiveCircuitCorrect x h w u i)
    (old:valid x h w r a) : valid x h w (r+1) (appendRegion x h w r a) := by
  let u:=r/x.n
  let i:=r%x.n
  have hu:u<x.rows:=(Nat.div_lt_iff_lt_mul hn).2 live
  have hi:i<x.n:=Nat.mod_lt _ hn
  have keep {p:ℕ} (j:ℕ) (hj:j<r) : (Function.update a.roots r p) j=a.roots j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have self:placed a.gates a.gates 0:=by refine ⟨by simp,?_⟩;intro p _;simp [relocateZero]
  by_cases mem:i∈keys x u
  · by_cases pos:0<scale x u
    · let c:=regionalCircuit x (piece x u i) (scale x u) h w
      obtain ⟨root,sound,complete⟩:=correct u hu i hi mem pos
      let b:Assembly:=⟨append a.gates c.1,Function.update a.roots r (a.gates.size+c.2)⟩
      have next:appendRegion x h w r a=b:=by simp only [appendRegion,show r%x.n∈keys x (r/x.n) from mem,if_pos,
        show 0<scale x (r/x.n) from pos] <;> rfl
      rw [next]
      apply advance x h w r a b old (append_placements a.gates c.1).1 keep
      change slot x h w r (append a.gates c.1) ((Function.update a.roots r (a.gates.size+c.2)) r)
      rw [Function.update_self]
      have lang:Language x.n (append a.gates c.1) (a.gates.size+c.2)=Language x.n c.1 c.2:=by
        funext L;exact propext (placement_preserves_words _ _ _ (append_placements a.gates c.1).2 _ root L)
      have hr:c.2<c.1.size:=root
      refine ⟨by simp only [append,Array.size_append,Array.size_map];omega,?_⟩
      rw [lang]
      exact ⟨fun no=>False.elim (no mem),fun _ dry=>False.elim ((not_lt_of_ge dry) pos),fun _ _=>⟨sound,complete⟩⟩
    · let b:Assembly:={a with roots:=Function.update a.roots r 1}
      have next:appendRegion x h w r a=b:=by
        simp only [appendRegion,if_pos (show r%x.n∈keys x (r/x.n) from mem),if_neg (show ¬0<scale x (r/x.n) from pos)] <;> rfl
      rw [next];apply advance x h w r a b old self keep
      change slot x h w r a.gates ((Function.update a.roots r 1) r)
      rw [Function.update_self]
      exact ⟨by have:=old.1;omega,fun no=>False.elim (no mem),fun _ _ L=>default_stop x.n a.gates old.2.2.1 L,
        fun _ yes=>False.elim (pos yes)⟩
  · let b:Assembly:={a with roots:=Function.update a.roots r 0}
    have next:appendRegion x h w r a=b:=by simp only [appendRegion,if_neg (show r%x.n∉keys x (r/x.n) from mem)] <;> rfl
    rw [next];apply advance x h w r a b old self keep
    change slot x h w r a.gates ((Function.update a.roots r 0) r)
    rw [Function.update_self]
    have sz:0<a.gates.size:=by have:=old.1;omega
    exact ⟨sz,fun _ L=>default_word x.n a.gates sz old.2.1 L,fun yes=>False.elim (mem yes),fun yes=>False.elim (mem yes)⟩

theorem raw_valid (x:World) (h w R:ℕ) (hn:0<x.n) (bound:R≤x.rows*x.n)
    (correct:∀u<x.rows,∀i<x.n,i∈keys x u → 0<scale x u → LiveCircuitCorrect x h w u i) :
    valid x h w R (rawAssembly x h w R) := by
  induction R with
  | zero=>exact initial x h w
  | succ r ih=>
    rw [rawAssembly,List.range_succ,List.foldl_append]
    exact append_valid x h w r (rawAssembly x h w r) hn (by omega) correct (ih (by omega))
end StableMSR.Recovery.GlobalAssemblyProof
open StableMSR.Recovery.GlobalAssemblyProof
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleCodes
open StableMSR.Recovery.WindowProfiles (piece keys)
open StableMSR.Recovery.SingleWindows StableMSR.Recovery.SingleRAM
open scoped Classical
set_option autoImplicit false

theorem solution (x : World) (e : ℚ) (hn : 0 < x.n)
    (correct : ∀ u < x.rows, ∀ i < x.n, i ∈ keys x u → 0 < scale x u →
      LiveCircuitCorrect x (budget (e:ℝ)) (widthBound (e:ℝ)) u i) :
    let a := globalAssembly x (budget (e:ℝ)) (widthBound (e:ℝ))
    RegionalLanguage x e a.gates a.roots := by
  let h:=budget (e:ℝ)
  let w:=widthBound (e:ℝ)
  let R:=x.rows*x.n
  let a:=rawAssembly x h w R
  let b:=padAssembly a R
  have hraw:=raw_valid x h w R hn (le_refl _) correct
  obtain ⟨sz,first,_,prior⟩:=hraw
  change 2≤a.gates.size at sz
  have pref:placed a.gates b.gates 0:=prefix_placement a.gates _
  have mono:a.gates.size≤b.gates.size:=by simpa only [Nat.zero_add] using pref.1
  have room:R≤3*b.gates.size:=by
    have eq:b.gates.size=a.gates.size+((R+2)/3-a.gates.size):=by simp [b,padAssembly]
    omega
  change RegionalLanguage x e b.gates b.roots
  have zero:gateAt b.gates 0=gateAt a.gates 0:=by
    simpa only [Nat.zero_add,relocateZero] using pref.2 0 (by change 0<a.gates.size;omega)
  refine ⟨by change 0<b.gates.size;omega,zero.trans first,?_⟩
  intro u hu i hi
  let r:=u*x.n+i
  have hr:r<R:=by
    have next: (u+1)*x.n≤x.rows*x.n:=Nat.mul_le_mul_right _ (by omega)
    dsimp [r,R];rw [Nat.add_mul,Nat.one_mul] at next;omega
  have div:r/x.n=u:=by
    dsimp [r];rw [Nat.mul_comm u _,Nat.mul_add_div hn,Nat.div_eq_of_lt hi,Nat.add_zero]
  have rem:r%x.n=i:=by dsimp [r];simp [Nat.add_mod,Nat.mod_eq_of_lt hi]
  have sl:=transport_slot x h w r pref (prior r hr)
  obtain ⟨inside,sem⟩:=sl
  change a.roots r<b.gates.size at inside
  change r<3*b.gates.size ∧ a.roots r<3*b.gates.size ∧ _
  refine ⟨by omega,by omega,?_⟩
  change classifies x h w u i (Language x.n b.gates (a.roots r))
  simpa only [div,rem] using sem
